-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_coverage0007_parents_0128_0192
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T05:28:57.720712+00:00
-- url     : https://prove2.me/submissions/9b9adb8d-76f1-44e4-9741-60d17ffc17e9

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0128_0144
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_7_p128_144
private theorem rec13278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[830]? = some (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec13279 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[831]? = some (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec13283 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([130, 134] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[130,134],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[835]? = some (⟨260,(-1),[1,2,5,6,13,14],[130,134],884⟩) from rfl))
private theorem rec13290 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[842]? = some (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec13311 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131, 135] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[5,6],[131,135],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[863]? = some (⟨260,(-1),[5,6],[131,135],886⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0007_parents_0128_0144 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 128).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 7).take 1 = [⟨8,260,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false,[(261,⟨([1],[]),true,([1],[]),false,false,[]⟩),(262,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(263,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(264,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(265,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(306,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(322,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 128).take 16 = [⟨1,128,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,129,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,130,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,131,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,132,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,133,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,134,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,135,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,136,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,137,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,138,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,139,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,140,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,141,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,142,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,143,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec13278 5 128 (by decide) (by decide)
  · left
    exact rec13278 5 129 (by decide) (by decide)
  · left
    exact rec13283 5 130 (by decide) (by decide)
  · left
    exact rec13311 5 131 (by decide) (by decide)
  · left
    exact rec13278 5 132 (by decide) (by decide)
  · left
    exact rec13278 5 133 (by decide) (by decide)
  · left
    exact rec13283 5 134 (by decide) (by decide)
  · left
    exact rec13311 5 135 (by decide) (by decide)
  · left
    exact rec13290 5 136 (by decide) (by decide)
  · left
    exact rec13290 5 137 (by decide) (by decide)
  · left
    exact rec13279 5 138 (by decide) (by decide)
  · left
    exact rec13279 5 139 (by decide) (by decide)
  · left
    exact rec13290 5 140 (by decide) (by decide)
  · left
    exact rec13290 5 141 (by decide) (by decide)
  · left
    exact rec13279 5 142 (by decide) (by decide)
  · left
    exact rec13279 5 143 (by decide) (by decide)
end Section14Coverage_5_7_p128_144

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0128_0144


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0144_0160
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_7_p144_160
private theorem rec13278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[830]? = some (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec13279 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[831]? = some (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec13284 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[146],885⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[836]? = some (⟨260,(-1),[1,2,5,6,13,14],[146],885⟩) from rfl))
private theorem rec13285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 151, 171, 175, 187, 191] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[837]? = some (⟨260,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) from rfl))
private theorem rec13286 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[150],887⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[838]? = some (⟨260,(-1),[1,2,5,6,13,14],[150],887⟩) from rfl))
private theorem rec13290 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[842]? = some (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0007_parents_0144_0160 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 144).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 7).take 1 = [⟨8,260,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false,[(261,⟨([1],[]),true,([1],[]),false,false,[]⟩),(262,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(263,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(264,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(265,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(306,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(322,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 144).take 16 = [⟨1,144,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,145,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,146,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,147,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,148,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,149,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,150,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,151,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,152,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,153,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,154,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,155,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,156,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,157,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,158,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,159,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec13278 5 144 (by decide) (by decide)
  · left
    exact rec13278 5 145 (by decide) (by decide)
  · left
    exact rec13284 5 146 (by decide) (by decide)
  · left
    exact rec13285 5 147 (by decide) (by decide)
  · left
    exact rec13278 5 148 (by decide) (by decide)
  · left
    exact rec13278 5 149 (by decide) (by decide)
  · left
    exact rec13286 5 150 (by decide) (by decide)
  · left
    exact rec13285 5 151 (by decide) (by decide)
  · left
    exact rec13290 5 152 (by decide) (by decide)
  · left
    exact rec13290 5 153 (by decide) (by decide)
  · left
    exact rec13279 5 154 (by decide) (by decide)
  · left
    exact rec13279 5 155 (by decide) (by decide)
  · left
    exact rec13290 5 156 (by decide) (by decide)
  · left
    exact rec13290 5 157 (by decide) (by decide)
  · left
    exact rec13279 5 158 (by decide) (by decide)
  · left
    exact rec13279 5 159 (by decide) (by decide)
end Section14Coverage_5_7_p144_160

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0144_0160


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0160_0176
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_7_p160_176
private theorem rec13278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[830]? = some (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec13279 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[831]? = some (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec13285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 151, 171, 175, 187, 191] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[837]? = some (⟨260,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) from rfl))
private theorem rec13287 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[174],908⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[839]? = some (⟨260,(-1),[1,2,5,6,13,14],[174],908⟩) from rfl))
private theorem rec13290 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[842]? = some (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec13330 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(0),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[882]? = some (⟨262,(0),[5],[170],3⟩) from rfl))
private theorem rec13332 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(1),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[884]? = some (⟨262,(1),[5],[170],3⟩) from rfl))
private theorem rec13334 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(2),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[886]? = some (⟨262,(2),[5],[170],3⟩) from rfl))
private theorem rec13336 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(3),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[888]? = some (⟨262,(3),[5],[170],3⟩) from rfl))
private theorem rec13338 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(4),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[890]? = some (⟨262,(4),[5],[170],3⟩) from rfl))
private theorem rec13340 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(5),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[892]? = some (⟨262,(5),[5],[170],3⟩) from rfl))
private theorem rec13342 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(6),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[894]? = some (⟨262,(6),[5],[170],3⟩) from rfl))
private theorem rec13344 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(7),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[896]? = some (⟨262,(7),[5],[170],3⟩) from rfl))
private theorem rec13346 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(8),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[898]? = some (⟨262,(8),[5],[170],3⟩) from rfl))
private theorem rec13348 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(9),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[900]? = some (⟨262,(9),[5],[170],3⟩) from rfl))
private theorem rec13350 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(10),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[902]? = some (⟨262,(10),[5],[170],3⟩) from rfl))
private theorem rec13352 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(11),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[904]? = some (⟨262,(11),[5],[170],3⟩) from rfl))
private theorem rec13354 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(12),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[906]? = some (⟨262,(12),[5],[170],3⟩) from rfl))
private theorem rec13356 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(13),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[908]? = some (⟨262,(13),[5],[170],3⟩) from rfl))
private theorem rec13358 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(14),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[910]? = some (⟨262,(14),[5],[170],3⟩) from rfl))
private theorem rec13360 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(15),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[912]? = some (⟨262,(15),[5],[170],3⟩) from rfl))
private theorem rec13362 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(16),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[914]? = some (⟨262,(16),[5],[170],3⟩) from rfl))
private theorem rec13364 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(17),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[916]? = some (⟨262,(17),[5],[170],3⟩) from rfl))
private theorem rec13366 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(18),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[918]? = some (⟨262,(18),[5],[170],3⟩) from rfl))
private theorem rec13368 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(19),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[920]? = some (⟨262,(19),[5],[170],3⟩) from rfl))
private theorem rec13370 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(20),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[922]? = some (⟨262,(20),[5],[170],3⟩) from rfl))
private theorem rec13372 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(21),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[924]? = some (⟨262,(21),[5],[170],3⟩) from rfl))
private theorem rec13374 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(22),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[926]? = some (⟨262,(22),[5],[170],3⟩) from rfl))
private theorem rec13376 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(23),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[928]? = some (⟨262,(23),[5],[170],3⟩) from rfl))
private theorem rec13378 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 262 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(24),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[930]? = some (⟨262,(24),[5],[170],3⟩) from rfl))
private theorem rec13380 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(0),[5],[170],1407⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[932]? = some (⟨264,(0),[5],[170],1407⟩) from rfl))
private theorem rec13382 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(1),[5],[170],1408⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[934]? = some (⟨264,(1),[5],[170],1408⟩) from rfl))
private theorem rec13384 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(2),[5],[170],1407⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[936]? = some (⟨264,(2),[5],[170],1407⟩) from rfl))
private theorem rec13386 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(3),[5],[170],1409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[938]? = some (⟨264,(3),[5],[170],1409⟩) from rfl))
private theorem rec13388 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(4),[5],[170],1410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[940]? = some (⟨264,(4),[5],[170],1410⟩) from rfl))
private theorem rec13390 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(5),[5],[170],1407⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[942]? = some (⟨264,(5),[5],[170],1407⟩) from rfl))
private theorem rec13392 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(6),[5],[170],1408⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[944]? = some (⟨264,(6),[5],[170],1408⟩) from rfl))
private theorem rec13394 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(7),[5],[170],1407⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[946]? = some (⟨264,(7),[5],[170],1407⟩) from rfl))
private theorem rec13396 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(8),[5],[170],1409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[948]? = some (⟨264,(8),[5],[170],1409⟩) from rfl))
private theorem rec13398 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(9),[5],[170],1410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[950]? = some (⟨264,(9),[5],[170],1410⟩) from rfl))
private theorem rec13400 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(10),[5],[170],1411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[952]? = some (⟨264,(10),[5],[170],1411⟩) from rfl))
private theorem rec13402 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(11),[5],[170],1411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[954]? = some (⟨264,(11),[5],[170],1411⟩) from rfl))
private theorem rec13404 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(12),[5],[170],1411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[956]? = some (⟨264,(12),[5],[170],1411⟩) from rfl))
private theorem rec13406 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(13),[5],[170],1411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[958]? = some (⟨264,(13),[5],[170],1411⟩) from rfl))
private theorem rec13408 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(14),[5],[170],1410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[960]? = some (⟨264,(14),[5],[170],1410⟩) from rfl))
private theorem rec13410 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(15),[5],[170],1412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[962]? = some (⟨264,(15),[5],[170],1412⟩) from rfl))
private theorem rec13412 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(16),[5],[170],1412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[964]? = some (⟨264,(16),[5],[170],1412⟩) from rfl))
private theorem rec13414 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(17),[5],[170],1412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[966]? = some (⟨264,(17),[5],[170],1412⟩) from rfl))
private theorem rec13416 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(18),[5],[170],1412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[968]? = some (⟨264,(18),[5],[170],1412⟩) from rfl))
private theorem rec13418 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(19),[5],[170],1412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[970]? = some (⟨264,(19),[5],[170],1412⟩) from rfl))
private theorem rec13420 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(20),[5],[170],1413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[972]? = some (⟨264,(20),[5],[170],1413⟩) from rfl))
private theorem rec13422 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(21),[5],[170],1413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[974]? = some (⟨264,(21),[5],[170],1413⟩) from rfl))
private theorem rec13424 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(22),[5],[170],1413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[976]? = some (⟨264,(22),[5],[170],1413⟩) from rfl))
private theorem rec13426 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(23),[5],[170],1413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[978]? = some (⟨264,(23),[5],[170],1413⟩) from rfl))
private theorem rec13428 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 264 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(24),[5],[170],1413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[980]? = some (⟨264,(24),[5],[170],1413⟩) from rfl))
private theorem rec13430 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(0),[5],[170],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[982]? = some (⟨267,(0),[5],[170],1086⟩) from rfl))
private theorem rec13433 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(1),[5],[170],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[985]? = some (⟨267,(1),[5],[170],1087⟩) from rfl))
private theorem rec13436 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(2),[5],[170],1088⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[988]? = some (⟨267,(2),[5],[170],1088⟩) from rfl))
private theorem rec13439 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(3),[5],[170],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[991]? = some (⟨267,(3),[5],[170],1089⟩) from rfl))
private theorem rec13442 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(4),[5],[170],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[994]? = some (⟨267,(4),[5],[170],1086⟩) from rfl))
private theorem rec13445 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(5),[5],[170],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[997]? = some (⟨267,(5),[5],[170],1087⟩) from rfl))
private theorem rec13448 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(6),[5],[170],1090⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1000]? = some (⟨267,(6),[5],[170],1090⟩) from rfl))
private theorem rec13451 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(7),[5],[170],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1003]? = some (⟨267,(7),[5],[170],1089⟩) from rfl))
private theorem rec13454 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(8),[5],[170],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1006]? = some (⟨267,(8),[5],[170],1086⟩) from rfl))
private theorem rec13457 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(9),[5],[170],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1009]? = some (⟨267,(9),[5],[170],1087⟩) from rfl))
private theorem rec13460 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(10),[5],[170],1088⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1012]? = some (⟨267,(10),[5],[170],1088⟩) from rfl))
private theorem rec13463 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(11),[5],[170],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1015]? = some (⟨267,(11),[5],[170],1089⟩) from rfl))
private theorem rec13466 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(12),[5],[170],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1018]? = some (⟨267,(12),[5],[170],1086⟩) from rfl))
private theorem rec13469 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(13),[5],[170],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1021]? = some (⟨267,(13),[5],[170],1087⟩) from rfl))
private theorem rec13472 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(14),[5],[170],1091⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1024]? = some (⟨267,(14),[5],[170],1091⟩) from rfl))
private theorem rec13475 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 267 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(15),[5],[170],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1027]? = some (⟨267,(15),[5],[170],1089⟩) from rfl))
private theorem rec13478 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(0),[5],[170],1414⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1030]? = some (⟨270,(0),[5],[170],1414⟩) from rfl))
private theorem rec13481 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(1),[5],[170],1415⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1033]? = some (⟨270,(1),[5],[170],1415⟩) from rfl))
private theorem rec13484 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(2),[5],[170],1414⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1036]? = some (⟨270,(2),[5],[170],1414⟩) from rfl))
private theorem rec13487 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(3),[5],[170],1416⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1039]? = some (⟨270,(3),[5],[170],1416⟩) from rfl))
private theorem rec13490 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(4),[5],[170],1417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1042]? = some (⟨270,(4),[5],[170],1417⟩) from rfl))
private theorem rec13493 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(5),[5],[170],1417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1045]? = some (⟨270,(5),[5],[170],1417⟩) from rfl))
private theorem rec13496 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(6),[5],[170],1417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1048]? = some (⟨270,(6),[5],[170],1417⟩) from rfl))
private theorem rec13499 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(7),[5],[170],1417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1051]? = some (⟨270,(7),[5],[170],1417⟩) from rfl))
private theorem rec13502 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(8),[5],[170],1418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1054]? = some (⟨270,(8),[5],[170],1418⟩) from rfl))
private theorem rec13505 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(9),[5],[170],1418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1057]? = some (⟨270,(9),[5],[170],1418⟩) from rfl))
private theorem rec13508 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(10),[5],[170],1418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1060]? = some (⟨270,(10),[5],[170],1418⟩) from rfl))
private theorem rec13511 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(11),[5],[170],1418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1063]? = some (⟨270,(11),[5],[170],1418⟩) from rfl))
private theorem rec13514 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(12),[5],[170],1419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1066]? = some (⟨270,(12),[5],[170],1419⟩) from rfl))
private theorem rec13517 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(13),[5],[170],1419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1069]? = some (⟨270,(13),[5],[170],1419⟩) from rfl))
private theorem rec13520 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(14),[5],[170],1419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1072]? = some (⟨270,(14),[5],[170],1419⟩) from rfl))
private theorem rec13523 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 270 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(15),[5],[170],1419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1075]? = some (⟨270,(15),[5],[170],1419⟩) from rfl))
private theorem rec13526 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 273 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(0),[5],[170],1098⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1078]? = some (⟨273,(0),[5],[170],1098⟩) from rfl))
private theorem rec13529 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 273 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(1),[5],[170],1099⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1081]? = some (⟨273,(1),[5],[170],1099⟩) from rfl))
private theorem rec13532 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 273 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(2),[5],[170],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1084]? = some (⟨273,(2),[5],[170],1100⟩) from rfl))
private theorem rec13535 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 273 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(3),[5],[170],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1087]? = some (⟨273,(3),[5],[170],1100⟩) from rfl))
private theorem rec13538 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 273 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(4),[5],[170],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1090]? = some (⟨273,(4),[5],[170],1100⟩) from rfl))
private theorem rec13541 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 273 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(5),[5],[170],1098⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1093]? = some (⟨273,(5),[5],[170],1098⟩) from rfl))
private theorem rec13544 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 273 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(6),[5],[170],1099⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1096]? = some (⟨273,(6),[5],[170],1099⟩) from rfl))
private theorem rec13547 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 273 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(7),[5],[170],1101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1099]? = some (⟨273,(7),[5],[170],1101⟩) from rfl))
private theorem rec13550 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 273 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(8),[5],[170],1102⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1102]? = some (⟨273,(8),[5],[170],1102⟩) from rfl))
private theorem rec13553 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 273 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(9),[5],[170],1101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1105]? = some (⟨273,(9),[5],[170],1101⟩) from rfl))
private theorem rec13556 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 275 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(0),[5],[170],1420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1108]? = some (⟨275,(0),[5],[170],1420⟩) from rfl))
private theorem rec13559 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 275 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(1),[5],[170],1420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1111]? = some (⟨275,(1),[5],[170],1420⟩) from rfl))
private theorem rec13562 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 275 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(2),[5],[170],1421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1114]? = some (⟨275,(2),[5],[170],1421⟩) from rfl))
private theorem rec13565 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 275 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(3),[5],[170],1422⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1117]? = some (⟨275,(3),[5],[170],1422⟩) from rfl))
private theorem rec13568 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 275 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(4),[5],[170],1423⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1120]? = some (⟨275,(4),[5],[170],1423⟩) from rfl))
private theorem rec13571 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 275 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(5),[5],[170],1424⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1123]? = some (⟨275,(5),[5],[170],1424⟩) from rfl))
private theorem rec13574 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 275 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(6),[5],[170],1424⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1126]? = some (⟨275,(6),[5],[170],1424⟩) from rfl))
private theorem rec13577 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 275 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(7),[5],[170],1424⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1129]? = some (⟨275,(7),[5],[170],1424⟩) from rfl))
private theorem rec13580 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 275 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(8),[5],[170],1422⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1132]? = some (⟨275,(8),[5],[170],1422⟩) from rfl))
private theorem rec13583 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 275 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(9),[5],[170],1423⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1135]? = some (⟨275,(9),[5],[170],1423⟩) from rfl))
private theorem rec13586 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(0),[5],[170],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1138]? = some (⟨278,(0),[5],[170],1108⟩) from rfl))
private theorem rec13589 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(1),[5],[170],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1141]? = some (⟨278,(1),[5],[170],1109⟩) from rfl))
private theorem rec13592 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(2),[5],[170],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1144]? = some (⟨278,(2),[5],[170],1110⟩) from rfl))
private theorem rec13595 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(3),[5],[170],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1147]? = some (⟨278,(3),[5],[170],1110⟩) from rfl))
private theorem rec13598 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(4),[5],[170],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1150]? = some (⟨278,(4),[5],[170],1110⟩) from rfl))
private theorem rec13601 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(5),[5],[170],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1153]? = some (⟨278,(5),[5],[170],1108⟩) from rfl))
private theorem rec13604 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(6),[5],[170],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1]? = some (⟨278,(6),[5],[170],1109⟩) from rfl))
private theorem rec13607 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(7),[5],[170],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[4]? = some (⟨278,(7),[5],[170],1111⟩) from rfl))
private theorem rec13610 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(8),[5],[170],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[7]? = some (⟨278,(8),[5],[170],1112⟩) from rfl))
private theorem rec13613 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(9),[5],[170],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[10]? = some (⟨278,(9),[5],[170],1111⟩) from rfl))
private theorem rec13616 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(10),[5],[170],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[13]? = some (⟨278,(10),[5],[170],1108⟩) from rfl))
private theorem rec13619 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(11),[5],[170],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[16]? = some (⟨278,(11),[5],[170],1109⟩) from rfl))
private theorem rec13622 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(12),[5],[170],1113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[19]? = some (⟨278,(12),[5],[170],1113⟩) from rfl))
private theorem rec13625 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(13),[5],[170],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[22]? = some (⟨278,(13),[5],[170],1112⟩) from rfl))
private theorem rec13628 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(14),[5],[170],1113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[25]? = some (⟨278,(14),[5],[170],1113⟩) from rfl))
private theorem rec13631 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(15),[5],[170],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[28]? = some (⟨278,(15),[5],[170],1108⟩) from rfl))
private theorem rec13634 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(16),[5],[170],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[31]? = some (⟨278,(16),[5],[170],1109⟩) from rfl))
private theorem rec13637 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(17),[5],[170],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[34]? = some (⟨278,(17),[5],[170],1111⟩) from rfl))
private theorem rec13640 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(18),[5],[170],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[37]? = some (⟨278,(18),[5],[170],1112⟩) from rfl))
private theorem rec13643 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(19),[5],[170],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[40]? = some (⟨278,(19),[5],[170],1111⟩) from rfl))
private theorem rec13646 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(20),[5],[170],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[43]? = some (⟨278,(20),[5],[170],1108⟩) from rfl))
private theorem rec13649 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(21),[5],[170],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[46]? = some (⟨278,(21),[5],[170],1109⟩) from rfl))
private theorem rec13652 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(22),[5],[170],1114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[49]? = some (⟨278,(22),[5],[170],1114⟩) from rfl))
private theorem rec13655 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(23),[5],[170],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[52]? = some (⟨278,(23),[5],[170],1112⟩) from rfl))
private theorem rec13658 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 278 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(24),[5],[170],1114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[55]? = some (⟨278,(24),[5],[170],1114⟩) from rfl))
private theorem rec13661 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 280 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(0),[5],[170],1425⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[58]? = some (⟨280,(0),[5],[170],1425⟩) from rfl))
private theorem rec13664 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 280 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(1),[5],[170],1425⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[61]? = some (⟨280,(1),[5],[170],1425⟩) from rfl))
private theorem rec13667 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 280 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(2),[5],[170],1426⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[64]? = some (⟨280,(2),[5],[170],1426⟩) from rfl))
private theorem rec13670 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 280 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(3),[5],[170],1427⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[67]? = some (⟨280,(3),[5],[170],1427⟩) from rfl))
private theorem rec13673 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 280 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(4),[5],[170],1428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[70]? = some (⟨280,(4),[5],[170],1428⟩) from rfl))
private theorem rec13676 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 280 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(5),[5],[170],1429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[73]? = some (⟨280,(5),[5],[170],1429⟩) from rfl))
private theorem rec13679 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 280 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(6),[5],[170],1429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[76]? = some (⟨280,(6),[5],[170],1429⟩) from rfl))
private theorem rec13682 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 280 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(7),[5],[170],1429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[79]? = some (⟨280,(7),[5],[170],1429⟩) from rfl))
private theorem rec13685 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 280 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(8),[5],[170],1427⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[82]? = some (⟨280,(8),[5],[170],1427⟩) from rfl))
private theorem rec13688 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 280 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(9),[5],[170],1428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[85]? = some (⟨280,(9),[5],[170],1428⟩) from rfl))
private theorem rec13691 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 283 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(0),[5],[170],1120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[88]? = some (⟨283,(0),[5],[170],1120⟩) from rfl))
private theorem rec13694 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 283 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(1),[5],[170],1121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[91]? = some (⟨283,(1),[5],[170],1121⟩) from rfl))
private theorem rec13697 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 283 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(2),[5],[170],1122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[94]? = some (⟨283,(2),[5],[170],1122⟩) from rfl))
private theorem rec13700 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 283 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(3),[5],[170],1122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[97]? = some (⟨283,(3),[5],[170],1122⟩) from rfl))
private theorem rec13703 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 283 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(4),[5],[170],1123⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[100]? = some (⟨283,(4),[5],[170],1123⟩) from rfl))
private theorem rec13706 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 283 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(5),[5],[170],1120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[103]? = some (⟨283,(5),[5],[170],1120⟩) from rfl))
private theorem rec13709 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 283 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(6),[5],[170],1121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[106]? = some (⟨283,(6),[5],[170],1121⟩) from rfl))
private theorem rec13712 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 283 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(7),[5],[170],1124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[109]? = some (⟨283,(7),[5],[170],1124⟩) from rfl))
private theorem rec13715 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 283 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(8),[5],[170],1125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[112]? = some (⟨283,(8),[5],[170],1125⟩) from rfl))
private theorem rec13718 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 283 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(9),[5],[170],1126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[115]? = some (⟨283,(9),[5],[170],1126⟩) from rfl))
private theorem rec13721 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(0),[5],[170],1430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[118]? = some (⟨285,(0),[5],[170],1430⟩) from rfl))
private theorem rec13724 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(1),[5],[170],1430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[121]? = some (⟨285,(1),[5],[170],1430⟩) from rfl))
private theorem rec13727 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(2),[5],[170],1431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[124]? = some (⟨285,(2),[5],[170],1431⟩) from rfl))
private theorem rec13730 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(3),[5],[170],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[127]? = some (⟨285,(3),[5],[170],1432⟩) from rfl))
private theorem rec13733 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(4),[5],[170],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[130]? = some (⟨285,(4),[5],[170],1433⟩) from rfl))
private theorem rec13736 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(5),[5],[170],1434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[133]? = some (⟨285,(5),[5],[170],1434⟩) from rfl))
private theorem rec13739 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(6),[5],[170],1434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[136]? = some (⟨285,(6),[5],[170],1434⟩) from rfl))
private theorem rec13742 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(7),[5],[170],1431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[139]? = some (⟨285,(7),[5],[170],1431⟩) from rfl))
private theorem rec13745 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(8),[5],[170],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[142]? = some (⟨285,(8),[5],[170],1432⟩) from rfl))
private theorem rec13748 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(9),[5],[170],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[145]? = some (⟨285,(9),[5],[170],1433⟩) from rfl))
private theorem rec13751 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(10),[5],[170],1430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[148]? = some (⟨285,(10),[5],[170],1430⟩) from rfl))
private theorem rec13754 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(11),[5],[170],1430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[151]? = some (⟨285,(11),[5],[170],1430⟩) from rfl))
private theorem rec13757 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(12),[5],[170],1431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[154]? = some (⟨285,(12),[5],[170],1431⟩) from rfl))
private theorem rec13760 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(13),[5],[170],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[157]? = some (⟨285,(13),[5],[170],1432⟩) from rfl))
private theorem rec13763 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(14),[5],[170],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[160]? = some (⟨285,(14),[5],[170],1433⟩) from rfl))
private theorem rec13766 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(15),[5],[170],1435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[163]? = some (⟨285,(15),[5],[170],1435⟩) from rfl))
private theorem rec13769 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(16),[5],[170],1435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[166]? = some (⟨285,(16),[5],[170],1435⟩) from rfl))
private theorem rec13772 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(17),[5],[170],1431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[169]? = some (⟨285,(17),[5],[170],1431⟩) from rfl))
private theorem rec13775 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(18),[5],[170],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[172]? = some (⟨285,(18),[5],[170],1432⟩) from rfl))
private theorem rec13778 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(19),[5],[170],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[175]? = some (⟨285,(19),[5],[170],1433⟩) from rfl))
private theorem rec13781 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(20),[5],[170],1436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[178]? = some (⟨285,(20),[5],[170],1436⟩) from rfl))
private theorem rec13784 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(21),[5],[170],1436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[181]? = some (⟨285,(21),[5],[170],1436⟩) from rfl))
private theorem rec13787 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(22),[5],[170],1436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[184]? = some (⟨285,(22),[5],[170],1436⟩) from rfl))
private theorem rec13790 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(23),[5],[170],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[187]? = some (⟨285,(23),[5],[170],1432⟩) from rfl))
private theorem rec13793 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 285 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(24),[5],[170],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[190]? = some (⟨285,(24),[5],[170],1433⟩) from rfl))
private theorem rec13796 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(0),[5],[170],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[193]? = some (⟨288,(0),[5],[170],1134⟩) from rfl))
private theorem rec13799 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(1),[5],[170],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[196]? = some (⟨288,(1),[5],[170],1135⟩) from rfl))
private theorem rec13802 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(2),[5],[170],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[199]? = some (⟨288,(2),[5],[170],1136⟩) from rfl))
private theorem rec13805 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(3),[5],[170],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[202]? = some (⟨288,(3),[5],[170],1136⟩) from rfl))
private theorem rec13808 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(4),[5],[170],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[205]? = some (⟨288,(4),[5],[170],1136⟩) from rfl))
private theorem rec13811 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(5),[5],[170],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[208]? = some (⟨288,(5),[5],[170],1134⟩) from rfl))
private theorem rec13814 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(6),[5],[170],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[211]? = some (⟨288,(6),[5],[170],1135⟩) from rfl))
private theorem rec13817 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(7),[5],[170],1137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[214]? = some (⟨288,(7),[5],[170],1137⟩) from rfl))
private theorem rec13820 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(8),[5],[170],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[217]? = some (⟨288,(8),[5],[170],1138⟩) from rfl))
private theorem rec13823 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(9),[5],[170],1137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[220]? = some (⟨288,(9),[5],[170],1137⟩) from rfl))
private theorem rec13826 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(10),[5],[170],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[223]? = some (⟨288,(10),[5],[170],1134⟩) from rfl))
private theorem rec13829 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(11),[5],[170],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[226]? = some (⟨288,(11),[5],[170],1135⟩) from rfl))
private theorem rec13832 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(12),[5],[170],1139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[229]? = some (⟨288,(12),[5],[170],1139⟩) from rfl))
private theorem rec13835 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(13),[5],[170],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[232]? = some (⟨288,(13),[5],[170],1138⟩) from rfl))
private theorem rec13838 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(14),[5],[170],1139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[235]? = some (⟨288,(14),[5],[170],1139⟩) from rfl))
private theorem rec13841 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(15),[5],[170],1140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[238]? = some (⟨288,(15),[5],[170],1140⟩) from rfl))
private theorem rec13844 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(16),[5],[170],1141⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[241]? = some (⟨288,(16),[5],[170],1141⟩) from rfl))
private theorem rec13847 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(17),[5],[170],1142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[244]? = some (⟨288,(17),[5],[170],1142⟩) from rfl))
private theorem rec13850 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(18),[5],[170],1143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[247]? = some (⟨288,(18),[5],[170],1143⟩) from rfl))
private theorem rec13853 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(19),[5],[170],1142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[250]? = some (⟨288,(19),[5],[170],1142⟩) from rfl))
private theorem rec13856 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(20),[5],[170],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[253]? = some (⟨288,(20),[5],[170],1134⟩) from rfl))
private theorem rec13859 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(21),[5],[170],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[256]? = some (⟨288,(21),[5],[170],1135⟩) from rfl))
private theorem rec13862 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(22),[5],[170],1144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[259]? = some (⟨288,(22),[5],[170],1144⟩) from rfl))
private theorem rec13865 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(23),[5],[170],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[262]? = some (⟨288,(23),[5],[170],1138⟩) from rfl))
private theorem rec13868 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 288 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(24),[5],[170],1144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[265]? = some (⟨288,(24),[5],[170],1144⟩) from rfl))
private theorem rec13871 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(0),[5],[170],1437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[268]? = some (⟨290,(0),[5],[170],1437⟩) from rfl))
private theorem rec13874 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(1),[5],[170],1437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[271]? = some (⟨290,(1),[5],[170],1437⟩) from rfl))
private theorem rec13877 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(2),[5],[170],1438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[274]? = some (⟨290,(2),[5],[170],1438⟩) from rfl))
private theorem rec13880 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(3),[5],[170],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[277]? = some (⟨290,(3),[5],[170],1439⟩) from rfl))
private theorem rec13883 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(4),[5],[170],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[280]? = some (⟨290,(4),[5],[170],1440⟩) from rfl))
private theorem rec13886 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(5),[5],[170],1441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[283]? = some (⟨290,(5),[5],[170],1441⟩) from rfl))
private theorem rec13889 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(6),[5],[170],1441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[286]? = some (⟨290,(6),[5],[170],1441⟩) from rfl))
private theorem rec13892 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(7),[5],[170],1438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[289]? = some (⟨290,(7),[5],[170],1438⟩) from rfl))
private theorem rec13895 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(8),[5],[170],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[292]? = some (⟨290,(8),[5],[170],1439⟩) from rfl))
private theorem rec13898 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(9),[5],[170],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[295]? = some (⟨290,(9),[5],[170],1440⟩) from rfl))
private theorem rec13901 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(10),[5],[170],1437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[298]? = some (⟨290,(10),[5],[170],1437⟩) from rfl))
private theorem rec13904 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(11),[5],[170],1437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[301]? = some (⟨290,(11),[5],[170],1437⟩) from rfl))
private theorem rec13907 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(12),[5],[170],1438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[304]? = some (⟨290,(12),[5],[170],1438⟩) from rfl))
private theorem rec13910 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(13),[5],[170],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[307]? = some (⟨290,(13),[5],[170],1439⟩) from rfl))
private theorem rec13913 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(14),[5],[170],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[310]? = some (⟨290,(14),[5],[170],1440⟩) from rfl))
private theorem rec13916 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(15),[5],[170],1442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[313]? = some (⟨290,(15),[5],[170],1442⟩) from rfl))
private theorem rec13919 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(16),[5],[170],1442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[316]? = some (⟨290,(16),[5],[170],1442⟩) from rfl))
private theorem rec13922 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(17),[5],[170],1438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[319]? = some (⟨290,(17),[5],[170],1438⟩) from rfl))
private theorem rec13925 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(18),[5],[170],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[322]? = some (⟨290,(18),[5],[170],1439⟩) from rfl))
private theorem rec13928 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(19),[5],[170],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[325]? = some (⟨290,(19),[5],[170],1440⟩) from rfl))
private theorem rec13931 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(20),[5],[170],1443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[328]? = some (⟨290,(20),[5],[170],1443⟩) from rfl))
private theorem rec13934 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(21),[5],[170],1443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[331]? = some (⟨290,(21),[5],[170],1443⟩) from rfl))
private theorem rec13937 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(22),[5],[170],1443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[334]? = some (⟨290,(22),[5],[170],1443⟩) from rfl))
private theorem rec13940 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(23),[5],[170],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[337]? = some (⟨290,(23),[5],[170],1439⟩) from rfl))
private theorem rec13943 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 290 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(24),[5],[170],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[340]? = some (⟨290,(24),[5],[170],1440⟩) from rfl))
private theorem rec13946 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(0),[5],[170],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[343]? = some (⟨293,(0),[5],[170],1152⟩) from rfl))
private theorem rec13949 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(1),[5],[170],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[346]? = some (⟨293,(1),[5],[170],1153⟩) from rfl))
private theorem rec13952 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(2),[5],[170],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[349]? = some (⟨293,(2),[5],[170],1154⟩) from rfl))
private theorem rec13955 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(3),[5],[170],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[352]? = some (⟨293,(3),[5],[170],1154⟩) from rfl))
private theorem rec13958 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(4),[5],[170],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[355]? = some (⟨293,(4),[5],[170],1154⟩) from rfl))
private theorem rec13961 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(5),[5],[170],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[358]? = some (⟨293,(5),[5],[170],1152⟩) from rfl))
private theorem rec13964 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(6),[5],[170],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[361]? = some (⟨293,(6),[5],[170],1153⟩) from rfl))
private theorem rec13967 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(7),[5],[170],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[364]? = some (⟨293,(7),[5],[170],1155⟩) from rfl))
private theorem rec13970 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(8),[5],[170],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[367]? = some (⟨293,(8),[5],[170],1156⟩) from rfl))
private theorem rec13973 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(9),[5],[170],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[370]? = some (⟨293,(9),[5],[170],1155⟩) from rfl))
private theorem rec13976 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(10),[5],[170],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[373]? = some (⟨293,(10),[5],[170],1152⟩) from rfl))
private theorem rec13979 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(11),[5],[170],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[376]? = some (⟨293,(11),[5],[170],1153⟩) from rfl))
private theorem rec13982 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(12),[5],[170],1157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[379]? = some (⟨293,(12),[5],[170],1157⟩) from rfl))
private theorem rec13985 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(13),[5],[170],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[382]? = some (⟨293,(13),[5],[170],1156⟩) from rfl))
private theorem rec13988 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(14),[5],[170],1157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[385]? = some (⟨293,(14),[5],[170],1157⟩) from rfl))
private theorem rec13991 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(15),[5],[170],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[388]? = some (⟨293,(15),[5],[170],1152⟩) from rfl))
private theorem rec13994 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(16),[5],[170],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[391]? = some (⟨293,(16),[5],[170],1153⟩) from rfl))
private theorem rec13997 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(17),[5],[170],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[394]? = some (⟨293,(17),[5],[170],1155⟩) from rfl))
private theorem rec14000 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(18),[5],[170],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[397]? = some (⟨293,(18),[5],[170],1156⟩) from rfl))
private theorem rec14003 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(19),[5],[170],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[400]? = some (⟨293,(19),[5],[170],1155⟩) from rfl))
private theorem rec14006 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(20),[5],[170],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[403]? = some (⟨293,(20),[5],[170],1152⟩) from rfl))
private theorem rec14009 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(21),[5],[170],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[406]? = some (⟨293,(21),[5],[170],1153⟩) from rfl))
private theorem rec14012 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(22),[5],[170],1158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[409]? = some (⟨293,(22),[5],[170],1158⟩) from rfl))
private theorem rec14015 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(23),[5],[170],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[412]? = some (⟨293,(23),[5],[170],1156⟩) from rfl))
private theorem rec14018 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 293 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(24),[5],[170],1158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[415]? = some (⟨293,(24),[5],[170],1158⟩) from rfl))
private theorem rec14021 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(0),[5],[170],1444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[418]? = some (⟨295,(0),[5],[170],1444⟩) from rfl))
private theorem rec14024 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(1),[5],[170],1444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[421]? = some (⟨295,(1),[5],[170],1444⟩) from rfl))
private theorem rec14027 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(2),[5],[170],1445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[424]? = some (⟨295,(2),[5],[170],1445⟩) from rfl))
private theorem rec14030 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(3),[5],[170],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[427]? = some (⟨295,(3),[5],[170],1446⟩) from rfl))
private theorem rec14033 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(4),[5],[170],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[430]? = some (⟨295,(4),[5],[170],1447⟩) from rfl))
private theorem rec14036 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(5),[5],[170],1448⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[433]? = some (⟨295,(5),[5],[170],1448⟩) from rfl))
private theorem rec14039 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(6),[5],[170],1448⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[436]? = some (⟨295,(6),[5],[170],1448⟩) from rfl))
private theorem rec14042 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(7),[5],[170],1445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[439]? = some (⟨295,(7),[5],[170],1445⟩) from rfl))
private theorem rec14045 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(8),[5],[170],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[442]? = some (⟨295,(8),[5],[170],1446⟩) from rfl))
private theorem rec14048 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(9),[5],[170],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[445]? = some (⟨295,(9),[5],[170],1447⟩) from rfl))
private theorem rec14051 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(10),[5],[170],1444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[448]? = some (⟨295,(10),[5],[170],1444⟩) from rfl))
private theorem rec14054 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(11),[5],[170],1444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[451]? = some (⟨295,(11),[5],[170],1444⟩) from rfl))
private theorem rec14057 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(12),[5],[170],1445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[454]? = some (⟨295,(12),[5],[170],1445⟩) from rfl))
private theorem rec14060 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(13),[5],[170],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[457]? = some (⟨295,(13),[5],[170],1446⟩) from rfl))
private theorem rec14063 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(14),[5],[170],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[460]? = some (⟨295,(14),[5],[170],1447⟩) from rfl))
private theorem rec14066 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(15),[5],[170],1449⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[463]? = some (⟨295,(15),[5],[170],1449⟩) from rfl))
private theorem rec14069 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(16),[5],[170],1449⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[466]? = some (⟨295,(16),[5],[170],1449⟩) from rfl))
private theorem rec14072 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(17),[5],[170],1445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[469]? = some (⟨295,(17),[5],[170],1445⟩) from rfl))
private theorem rec14075 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(18),[5],[170],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[472]? = some (⟨295,(18),[5],[170],1446⟩) from rfl))
private theorem rec14078 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(19),[5],[170],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[475]? = some (⟨295,(19),[5],[170],1447⟩) from rfl))
private theorem rec14081 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(20),[5],[170],1450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[478]? = some (⟨295,(20),[5],[170],1450⟩) from rfl))
private theorem rec14084 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(21),[5],[170],1450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[481]? = some (⟨295,(21),[5],[170],1450⟩) from rfl))
private theorem rec14087 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(22),[5],[170],1450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[484]? = some (⟨295,(22),[5],[170],1450⟩) from rfl))
private theorem rec14090 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(23),[5],[170],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[487]? = some (⟨295,(23),[5],[170],1446⟩) from rfl))
private theorem rec14093 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 295 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(24),[5],[170],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[490]? = some (⟨295,(24),[5],[170],1447⟩) from rfl))
private theorem rec14096 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(0),[5],[170],1451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[493]? = some (⟨297,(0),[5],[170],1451⟩) from rfl))
private theorem rec14099 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(1),[5],[170],1452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[496]? = some (⟨297,(1),[5],[170],1452⟩) from rfl))
private theorem rec14102 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(2),[5],[170],1453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[499]? = some (⟨297,(2),[5],[170],1453⟩) from rfl))
private theorem rec14105 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(3),[5],[170],1454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[502]? = some (⟨297,(3),[5],[170],1454⟩) from rfl))
private theorem rec14108 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(4),[5],[170],1451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[505]? = some (⟨297,(4),[5],[170],1451⟩) from rfl))
private theorem rec14111 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(5),[5],[170],1452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[508]? = some (⟨297,(5),[5],[170],1452⟩) from rfl))
private theorem rec14114 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(6),[5],[170],1455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[511]? = some (⟨297,(6),[5],[170],1455⟩) from rfl))
private theorem rec14117 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(7),[5],[170],1454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[514]? = some (⟨297,(7),[5],[170],1454⟩) from rfl))
private theorem rec14120 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(8),[5],[170],1451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[517]? = some (⟨297,(8),[5],[170],1451⟩) from rfl))
private theorem rec14123 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(9),[5],[170],1452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[520]? = some (⟨297,(9),[5],[170],1452⟩) from rfl))
private theorem rec14126 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(10),[5],[170],1453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[523]? = some (⟨297,(10),[5],[170],1453⟩) from rfl))
private theorem rec14129 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(11),[5],[170],1454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[526]? = some (⟨297,(11),[5],[170],1454⟩) from rfl))
private theorem rec14132 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(12),[5],[170],1451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[529]? = some (⟨297,(12),[5],[170],1451⟩) from rfl))
private theorem rec14135 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(13),[5],[170],1452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[532]? = some (⟨297,(13),[5],[170],1452⟩) from rfl))
private theorem rec14138 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(14),[5],[170],1456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[535]? = some (⟨297,(14),[5],[170],1456⟩) from rfl))
private theorem rec14141 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 297 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(15),[5],[170],1454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[538]? = some (⟨297,(15),[5],[170],1454⟩) from rfl))
private theorem rec14144 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(0),[5],[170],1457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[541]? = some (⟨300,(0),[5],[170],1457⟩) from rfl))
private theorem rec14147 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(1),[5],[170],1458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[544]? = some (⟨300,(1),[5],[170],1458⟩) from rfl))
private theorem rec14150 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(2),[5],[170],1457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[547]? = some (⟨300,(2),[5],[170],1457⟩) from rfl))
private theorem rec14153 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(3),[5],[170],1459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[550]? = some (⟨300,(3),[5],[170],1459⟩) from rfl))
private theorem rec14156 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(4),[5],[170],1460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[553]? = some (⟨300,(4),[5],[170],1460⟩) from rfl))
private theorem rec14159 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(5),[5],[170],1460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[556]? = some (⟨300,(5),[5],[170],1460⟩) from rfl))
private theorem rec14162 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(6),[5],[170],1460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[559]? = some (⟨300,(6),[5],[170],1460⟩) from rfl))
private theorem rec14165 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(7),[5],[170],1460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[562]? = some (⟨300,(7),[5],[170],1460⟩) from rfl))
private theorem rec14168 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(8),[5],[170],1461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[565]? = some (⟨300,(8),[5],[170],1461⟩) from rfl))
private theorem rec14171 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(9),[5],[170],1461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[568]? = some (⟨300,(9),[5],[170],1461⟩) from rfl))
private theorem rec14174 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(10),[5],[170],1461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[571]? = some (⟨300,(10),[5],[170],1461⟩) from rfl))
private theorem rec14177 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(11),[5],[170],1461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[574]? = some (⟨300,(11),[5],[170],1461⟩) from rfl))
private theorem rec14180 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(12),[5],[170],1462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[577]? = some (⟨300,(12),[5],[170],1462⟩) from rfl))
private theorem rec14183 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(13),[5],[170],1462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[580]? = some (⟨300,(13),[5],[170],1462⟩) from rfl))
private theorem rec14186 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(14),[5],[170],1462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[583]? = some (⟨300,(14),[5],[170],1462⟩) from rfl))
private theorem rec14189 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 300 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(15),[5],[170],1462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[586]? = some (⟨300,(15),[5],[170],1462⟩) from rfl))
private theorem rec14192 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(0),[5],[170],1463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[589]? = some (⟨302,(0),[5],[170],1463⟩) from rfl))
private theorem rec14195 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(1),[5],[170],1464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[592]? = some (⟨302,(1),[5],[170],1464⟩) from rfl))
private theorem rec14198 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(2),[5],[170],1465⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[595]? = some (⟨302,(2),[5],[170],1465⟩) from rfl))
private theorem rec14201 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(3),[5],[170],1466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[598]? = some (⟨302,(3),[5],[170],1466⟩) from rfl))
private theorem rec14204 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(4),[5],[170],1463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[601]? = some (⟨302,(4),[5],[170],1463⟩) from rfl))
private theorem rec14207 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(5),[5],[170],1464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[604]? = some (⟨302,(5),[5],[170],1464⟩) from rfl))
private theorem rec14210 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(6),[5],[170],1467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[607]? = some (⟨302,(6),[5],[170],1467⟩) from rfl))
private theorem rec14213 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(7),[5],[170],1466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[610]? = some (⟨302,(7),[5],[170],1466⟩) from rfl))
private theorem rec14216 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(8),[5],[170],1463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[613]? = some (⟨302,(8),[5],[170],1463⟩) from rfl))
private theorem rec14219 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(9),[5],[170],1464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[616]? = some (⟨302,(9),[5],[170],1464⟩) from rfl))
private theorem rec14222 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(10),[5],[170],1465⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[619]? = some (⟨302,(10),[5],[170],1465⟩) from rfl))
private theorem rec14225 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(11),[5],[170],1466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[622]? = some (⟨302,(11),[5],[170],1466⟩) from rfl))
private theorem rec14228 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(12),[5],[170],1463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[625]? = some (⟨302,(12),[5],[170],1463⟩) from rfl))
private theorem rec14231 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(13),[5],[170],1464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[628]? = some (⟨302,(13),[5],[170],1464⟩) from rfl))
private theorem rec14234 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(14),[5],[170],1468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[631]? = some (⟨302,(14),[5],[170],1468⟩) from rfl))
private theorem rec14237 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 302 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(15),[5],[170],1466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[634]? = some (⟨302,(15),[5],[170],1466⟩) from rfl))
private theorem rec14240 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 305 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨305,(0),[5],[170],1469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[637]? = some (⟨305,(0),[5],[170],1469⟩) from rfl))
private theorem rec14243 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 305 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨305,(1),[5],[170],1470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[640]? = some (⟨305,(1),[5],[170],1470⟩) from rfl))
private theorem rec14246 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 305 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨305,(2),[5],[170],1471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[643]? = some (⟨305,(2),[5],[170],1471⟩) from rfl))
private theorem rec14249 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 305 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨305,(3),[5],[170],1472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[646]? = some (⟨305,(3),[5],[170],1472⟩) from rfl))
private theorem rec14252 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(0),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[649]? = some (⟨307,(0),[5],[170],3⟩) from rfl))
private theorem rec14255 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(1),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[652]? = some (⟨307,(1),[5],[170],3⟩) from rfl))
private theorem rec14258 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(2),[5],[170],1473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[655]? = some (⟨307,(2),[5],[170],1473⟩) from rfl))
private theorem rec14261 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(3),[5],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[658]? = some (⟨307,(3),[5],[170],29⟩) from rfl))
private theorem rec14264 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(4),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[661]? = some (⟨307,(4),[5],[170],3⟩) from rfl))
private theorem rec14267 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(5),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[664]? = some (⟨307,(5),[5],[170],3⟩) from rfl))
private theorem rec14270 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(6),[5],[170],511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[667]? = some (⟨307,(6),[5],[170],511⟩) from rfl))
private theorem rec14273 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(7),[5],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[670]? = some (⟨307,(7),[5],[170],29⟩) from rfl))
private theorem rec14276 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(8),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[673]? = some (⟨307,(8),[5],[170],3⟩) from rfl))
private theorem rec14279 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(9),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[676]? = some (⟨307,(9),[5],[170],3⟩) from rfl))
private theorem rec14282 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(10),[5],[170],512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[679]? = some (⟨307,(10),[5],[170],512⟩) from rfl))
private theorem rec14285 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(11),[5],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[682]? = some (⟨307,(11),[5],[170],29⟩) from rfl))
private theorem rec14288 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(12),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[685]? = some (⟨307,(12),[5],[170],3⟩) from rfl))
private theorem rec14291 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(13),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[688]? = some (⟨307,(13),[5],[170],3⟩) from rfl))
private theorem rec14294 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(14),[5],[170],513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[691]? = some (⟨307,(14),[5],[170],513⟩) from rfl))
private theorem rec14297 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(15),[5],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[694]? = some (⟨307,(15),[5],[170],29⟩) from rfl))
private theorem rec14300 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(16),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[697]? = some (⟨307,(16),[5],[170],3⟩) from rfl))
private theorem rec14303 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(17),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[700]? = some (⟨307,(17),[5],[170],3⟩) from rfl))
private theorem rec14306 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(18),[5],[170],514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[703]? = some (⟨307,(18),[5],[170],514⟩) from rfl))
private theorem rec14309 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 307 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(19),[5],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[706]? = some (⟨307,(19),[5],[170],29⟩) from rfl))
private theorem rec14312 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 308 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨308,(8),[5],[170],1474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[709]? = some (⟨308,(8),[5],[170],1474⟩) from rfl))
private theorem rec14315 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 308 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨308,(9),[5],[170],1475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[712]? = some (⟨308,(9),[5],[170],1475⟩) from rfl))
private theorem rec14318 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 308 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨308,(10),[5],[170],1474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[715]? = some (⟨308,(10),[5],[170],1474⟩) from rfl))
private theorem rec14321 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 308 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨308,(11),[5],[170],1476⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[718]? = some (⟨308,(11),[5],[170],1476⟩) from rfl))
private theorem rec14324 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 309 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(0),[5],[170],1188⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[721]? = some (⟨309,(0),[5],[170],1188⟩) from rfl))
private theorem rec14327 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 309 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(1),[5],[170],1189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[724]? = some (⟨309,(1),[5],[170],1189⟩) from rfl))
private theorem rec14330 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 309 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(2),[5],[170],1190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[727]? = some (⟨309,(2),[5],[170],1190⟩) from rfl))
private theorem rec14333 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 309 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(3),[5],[170],1191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[730]? = some (⟨309,(3),[5],[170],1191⟩) from rfl))
private theorem rec14336 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 309 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(4),[5],[170],1477⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[733]? = some (⟨309,(4),[5],[170],1477⟩) from rfl))
private theorem rec14339 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 311 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨311,(0),[5],[170],1478⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[736]? = some (⟨311,(0),[5],[170],1478⟩) from rfl))
private theorem rec14342 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 311 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨311,(1),[5],[170],1479⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[739]? = some (⟨311,(1),[5],[170],1479⟩) from rfl))
private theorem rec14345 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 311 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨311,(2),[5],[170],1480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[742]? = some (⟨311,(2),[5],[170],1480⟩) from rfl))
private theorem rec14348 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 311 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨311,(3),[5],[170],1481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[745]? = some (⟨311,(3),[5],[170],1481⟩) from rfl))
private theorem rec14351 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 312 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨312,(0),[5],[170],1482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[748]? = some (⟨312,(0),[5],[170],1482⟩) from rfl))
private theorem rec14354 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 312 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨312,(1),[5],[170],1483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[751]? = some (⟨312,(1),[5],[170],1483⟩) from rfl))
private theorem rec14357 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 312 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨312,(2),[5],[170],1482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[754]? = some (⟨312,(2),[5],[170],1482⟩) from rfl))
private theorem rec14360 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 312 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨312,(3),[5],[170],1484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[757]? = some (⟨312,(3),[5],[170],1484⟩) from rfl))
private theorem rec14363 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 313 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨313,(0),[5],[170],1200⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[760]? = some (⟨313,(0),[5],[170],1200⟩) from rfl))
private theorem rec14366 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 313 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨313,(1),[5],[170],1201⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[763]? = some (⟨313,(1),[5],[170],1201⟩) from rfl))
private theorem rec14369 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 313 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨313,(2),[5],[170],1202⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[766]? = some (⟨313,(2),[5],[170],1202⟩) from rfl))
private theorem rec14372 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 313 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨313,(3),[5],[170],1203⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[769]? = some (⟨313,(3),[5],[170],1203⟩) from rfl))
private theorem rec14376 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(0),[5],[170],1485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[773]? = some (⟨315,(0),[5],[170],1485⟩) from rfl))
private theorem rec14379 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(1),[5],[170],1486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[776]? = some (⟨315,(1),[5],[170],1486⟩) from rfl))
private theorem rec14382 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(2),[5],[170],1487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[779]? = some (⟨315,(2),[5],[170],1487⟩) from rfl))
private theorem rec14385 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(3),[5],[170],1488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[782]? = some (⟨315,(3),[5],[170],1488⟩) from rfl))
private theorem rec14388 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(4),[5],[170],1489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[785]? = some (⟨315,(4),[5],[170],1489⟩) from rfl))
private theorem rec14391 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(5),[5],[170],1486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[788]? = some (⟨315,(5),[5],[170],1486⟩) from rfl))
private theorem rec14394 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(6),[5],[170],1487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[791]? = some (⟨315,(6),[5],[170],1487⟩) from rfl))
private theorem rec14397 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(7),[5],[170],1488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[794]? = some (⟨315,(7),[5],[170],1488⟩) from rfl))
private theorem rec14400 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(8),[5],[170],1485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[797]? = some (⟨315,(8),[5],[170],1485⟩) from rfl))
private theorem rec14403 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(9),[5],[170],1490⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[800]? = some (⟨315,(9),[5],[170],1490⟩) from rfl))
private theorem rec14406 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(10),[5],[170],1487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[803]? = some (⟨315,(10),[5],[170],1487⟩) from rfl))
private theorem rec14409 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(11),[5],[170],1488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[806]? = some (⟨315,(11),[5],[170],1488⟩) from rfl))
private theorem rec14412 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(12),[5],[170],1491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[809]? = some (⟨315,(12),[5],[170],1491⟩) from rfl))
private theorem rec14415 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(13),[5],[170],1486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[812]? = some (⟨315,(13),[5],[170],1486⟩) from rfl))
private theorem rec14418 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(14),[5],[170],1487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[815]? = some (⟨315,(14),[5],[170],1487⟩) from rfl))
private theorem rec14421 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 315 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(15),[5],[170],1488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[818]? = some (⟨315,(15),[5],[170],1488⟩) from rfl))
private theorem rec14424 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(0),[5],[170],1211⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[821]? = some (⟨317,(0),[5],[170],1211⟩) from rfl))
private theorem rec14427 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(1),[5],[170],1212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[824]? = some (⟨317,(1),[5],[170],1212⟩) from rfl))
private theorem rec14430 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(2),[5],[170],1213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[827]? = some (⟨317,(2),[5],[170],1213⟩) from rfl))
private theorem rec14433 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(3),[5],[170],1214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[830]? = some (⟨317,(3),[5],[170],1214⟩) from rfl))
private theorem rec14436 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(4),[5],[170],1215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[833]? = some (⟨317,(4),[5],[170],1215⟩) from rfl))
private theorem rec14439 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(5),[5],[170],1216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[836]? = some (⟨317,(5),[5],[170],1216⟩) from rfl))
private theorem rec14442 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(6),[5],[170],1217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[839]? = some (⟨317,(6),[5],[170],1217⟩) from rfl))
private theorem rec14445 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(7),[5],[170],1218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[842]? = some (⟨317,(7),[5],[170],1218⟩) from rfl))
private theorem rec14448 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(8),[5],[170],1492⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[845]? = some (⟨317,(8),[5],[170],1492⟩) from rfl))
private theorem rec14451 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(9),[5],[170],1493⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[848]? = some (⟨317,(9),[5],[170],1493⟩) from rfl))
private theorem rec14454 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(10),[5],[170],1494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[851]? = some (⟨317,(10),[5],[170],1494⟩) from rfl))
private theorem rec14457 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(11),[5],[170],1495⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[854]? = some (⟨317,(11),[5],[170],1495⟩) from rfl))
private theorem rec14460 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(12),[5],[170],1496⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[857]? = some (⟨317,(12),[5],[170],1496⟩) from rfl))
private theorem rec14463 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(13),[5],[170],1493⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[860]? = some (⟨317,(13),[5],[170],1493⟩) from rfl))
private theorem rec14466 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(14),[5],[170],1494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[863]? = some (⟨317,(14),[5],[170],1494⟩) from rfl))
private theorem rec14469 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 317 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(15),[5],[170],1495⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[866]? = some (⟨317,(15),[5],[170],1495⟩) from rfl))
private theorem rec14472 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(0),[5],[170],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[869]? = some (⟨318,(0),[5],[170],882⟩) from rfl))
private theorem rec14475 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(1),[5],[170],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[872]? = some (⟨318,(1),[5],[170],1497⟩) from rfl))
private theorem rec14478 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(2),[5],[170],1498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[875]? = some (⟨318,(2),[5],[170],1498⟩) from rfl))
private theorem rec14481 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(3),[5],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[878]? = some (⟨318,(3),[5],[170],101⟩) from rfl))
private theorem rec14484 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(4),[5],[170],1498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[881]? = some (⟨318,(4),[5],[170],1498⟩) from rfl))
private theorem rec14487 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(5),[5],[170],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[884]? = some (⟨318,(5),[5],[170],882⟩) from rfl))
private theorem rec14490 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(6),[5],[170],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[887]? = some (⟨318,(6),[5],[170],1497⟩) from rfl))
private theorem rec14493 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(7),[5],[170],1499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[890]? = some (⟨318,(7),[5],[170],1499⟩) from rfl))
private theorem rec14496 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(8),[5],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[893]? = some (⟨318,(8),[5],[170],101⟩) from rfl))
private theorem rec14499 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(9),[5],[170],1499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[896]? = some (⟨318,(9),[5],[170],1499⟩) from rfl))
private theorem rec14502 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(10),[5],[170],1500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[899]? = some (⟨318,(10),[5],[170],1500⟩) from rfl))
private theorem rec14505 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(11),[5],[170],1501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[902]? = some (⟨318,(11),[5],[170],1501⟩) from rfl))
private theorem rec14508 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(12),[5],[170],1502⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[905]? = some (⟨318,(12),[5],[170],1502⟩) from rfl))
private theorem rec14511 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(13),[5],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[908]? = some (⟨318,(13),[5],[170],101⟩) from rfl))
private theorem rec14514 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(14),[5],[170],1502⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[911]? = some (⟨318,(14),[5],[170],1502⟩) from rfl))
private theorem rec14517 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(15),[5],[170],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[914]? = some (⟨318,(15),[5],[170],882⟩) from rfl))
private theorem rec14520 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(16),[5],[170],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[917]? = some (⟨318,(16),[5],[170],1497⟩) from rfl))
private theorem rec14523 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(17),[5],[170],1503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[920]? = some (⟨318,(17),[5],[170],1503⟩) from rfl))
private theorem rec14526 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(18),[5],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[923]? = some (⟨318,(18),[5],[170],101⟩) from rfl))
private theorem rec14529 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 318 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(19),[5],[170],1503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[926]? = some (⟨318,(19),[5],[170],1503⟩) from rfl))
private theorem rec14532 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(0),[5],[170],1231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[929]? = some (⟨319,(0),[5],[170],1231⟩) from rfl))
private theorem rec14535 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(1),[5],[170],1229⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[932]? = some (⟨319,(1),[5],[170],1229⟩) from rfl))
private theorem rec14538 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(2),[5],[170],1228⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[935]? = some (⟨319,(2),[5],[170],1228⟩) from rfl))
private theorem rec14541 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(3),[5],[170],1230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[938]? = some (⟨319,(3),[5],[170],1230⟩) from rfl))
private theorem rec14544 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(4),[5],[170],1231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[941]? = some (⟨319,(4),[5],[170],1231⟩) from rfl))
private theorem rec14547 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(5),[5],[170],1232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[944]? = some (⟨319,(5),[5],[170],1232⟩) from rfl))
private theorem rec14550 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(6),[5],[170],1504⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[947]? = some (⟨319,(6),[5],[170],1504⟩) from rfl))
private theorem rec14553 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(7),[5],[170],1505⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[950]? = some (⟨319,(7),[5],[170],1505⟩) from rfl))
private theorem rec14556 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(8),[5],[170],1235⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[953]? = some (⟨319,(8),[5],[170],1235⟩) from rfl))
private theorem rec14559 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(9),[5],[170],1236⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[956]? = some (⟨319,(9),[5],[170],1236⟩) from rfl))
private theorem rec14562 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(10),[5],[170],1506⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[959]? = some (⟨319,(10),[5],[170],1506⟩) from rfl))
private theorem rec14565 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(11),[5],[170],1507⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[962]? = some (⟨319,(11),[5],[170],1507⟩) from rfl))
private theorem rec14568 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(12),[5],[170],1239⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[965]? = some (⟨319,(12),[5],[170],1239⟩) from rfl))
private theorem rec14571 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(13),[5],[170],1240⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[968]? = some (⟨319,(13),[5],[170],1240⟩) from rfl))
private theorem rec14574 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(14),[5],[170],1508⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[971]? = some (⟨319,(14),[5],[170],1508⟩) from rfl))
private theorem rec14577 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(15),[5],[170],1508⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[974]? = some (⟨319,(15),[5],[170],1508⟩) from rfl))
private theorem rec14580 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(16),[5],[170],1242⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[977]? = some (⟨319,(16),[5],[170],1242⟩) from rfl))
private theorem rec14583 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(17),[5],[170],1243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[980]? = some (⟨319,(17),[5],[170],1243⟩) from rfl))
private theorem rec14586 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(18),[5],[170],1509⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[983]? = some (⟨319,(18),[5],[170],1509⟩) from rfl))
private theorem rec14589 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 319 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(19),[5],[170],1509⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[986]? = some (⟨319,(19),[5],[170],1509⟩) from rfl))
private theorem rec14592 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(0),[5],[170],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[989]? = some (⟨321,(0),[5],[170],882⟩) from rfl))
private theorem rec14595 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(1),[5],[170],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[992]? = some (⟨321,(1),[5],[170],1497⟩) from rfl))
private theorem rec14598 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(2),[5],[170],1245⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[995]? = some (⟨321,(2),[5],[170],1245⟩) from rfl))
private theorem rec14601 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(3),[5],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[998]? = some (⟨321,(3),[5],[170],101⟩) from rfl))
private theorem rec14604 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(4),[5],[170],1245⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1001]? = some (⟨321,(4),[5],[170],1245⟩) from rfl))
private theorem rec14607 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(5),[5],[170],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1004]? = some (⟨321,(5),[5],[170],882⟩) from rfl))
private theorem rec14610 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(6),[5],[170],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1007]? = some (⟨321,(6),[5],[170],1497⟩) from rfl))
private theorem rec14613 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(7),[5],[170],1510⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1010]? = some (⟨321,(7),[5],[170],1510⟩) from rfl))
private theorem rec14616 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(8),[5],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1013]? = some (⟨321,(8),[5],[170],101⟩) from rfl))
private theorem rec14619 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(9),[5],[170],1510⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1016]? = some (⟨321,(9),[5],[170],1510⟩) from rfl))
private theorem rec14622 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(10),[5],[170],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1019]? = some (⟨321,(10),[5],[170],882⟩) from rfl))
private theorem rec14625 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(11),[5],[170],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1022]? = some (⟨321,(11),[5],[170],1497⟩) from rfl))
private theorem rec14628 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(12),[5],[170],1511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1025]? = some (⟨321,(12),[5],[170],1511⟩) from rfl))
private theorem rec14631 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(13),[5],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1028]? = some (⟨321,(13),[5],[170],101⟩) from rfl))
private theorem rec14634 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(14),[5],[170],1511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1031]? = some (⟨321,(14),[5],[170],1511⟩) from rfl))
private theorem rec14637 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(15),[5],[170],625⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1034]? = some (⟨321,(15),[5],[170],625⟩) from rfl))
private theorem rec14640 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(16),[5],[170],626⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1037]? = some (⟨321,(16),[5],[170],626⟩) from rfl))
private theorem rec14643 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(17),[5],[170],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1040]? = some (⟨321,(17),[5],[170],286⟩) from rfl))
private theorem rec14646 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(18),[5],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1043]? = some (⟨321,(18),[5],[170],101⟩) from rfl))
private theorem rec14649 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(19),[5],[170],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1046]? = some (⟨321,(19),[5],[170],286⟩) from rfl))
private theorem rec14652 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(20),[5],[170],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1049]? = some (⟨321,(20),[5],[170],882⟩) from rfl))
private theorem rec14655 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(21),[5],[170],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1052]? = some (⟨321,(21),[5],[170],1497⟩) from rfl))
private theorem rec14658 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(22),[5],[170],1512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1055]? = some (⟨321,(22),[5],[170],1512⟩) from rfl))
private theorem rec14661 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(23),[5],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1058]? = some (⟨321,(23),[5],[170],101⟩) from rfl))
private theorem rec14664 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 321 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(24),[5],[170],1512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1061]? = some (⟨321,(24),[5],[170],1512⟩) from rfl))
private theorem rec14667 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 322 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨322,(5),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1064]? = some (⟨322,(5),[5],[170],3⟩) from rfl))
private theorem rec14668 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 322 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨322,(7),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1065]? = some (⟨322,(7),[5],[170],3⟩) from rfl))
private theorem rec14669 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 322 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨322,(8),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1066]? = some (⟨322,(8),[5],[170],3⟩) from rfl))
private theorem rec14670 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 322 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨322,(9),[5],[170],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1067]? = some (⟨322,(9),[5],[170],143⟩) from rfl))
private theorem rec14671 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 322 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨322,(15),[5],[170],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1068]? = some (⟨322,(15),[5],[170],48⟩) from rfl))
private theorem rec14672 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 322 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨322,(16),[5],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1069]? = some (⟨322,(16),[5],[170],3⟩) from rfl))
private theorem rec14673 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 322 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨322,(17),[5],[170],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1070]? = some (⟨322,(17),[5],[170],48⟩) from rfl))
private theorem rec14674 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 322 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨322,(19),[5],[170],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1071]? = some (⟨322,(19),[5],[170],143⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0007_parents_0160_0176 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 160).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 7).take 1 = [⟨8,260,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false,[(261,⟨([1],[]),true,([1],[]),false,false,[]⟩),(262,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(263,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(264,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(265,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(306,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(322,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 160).take 16 = [⟨1,160,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,161,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,162,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,163,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,164,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,165,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,166,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,167,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,168,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,169,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,170,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨1,171,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨1,172,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,173,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,174,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,175,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec13290 5 160 (by decide) (by decide)
  · left
    exact rec13290 5 161 (by decide) (by decide)
  · left
    exact rec13279 5 162 (by decide) (by decide)
  · left
    exact rec13279 5 163 (by decide) (by decide)
  · left
    exact rec13290 5 164 (by decide) (by decide)
  · left
    exact rec13290 5 165 (by decide) (by decide)
  · left
    exact rec13279 5 166 (by decide) (by decide)
  · left
    exact rec13279 5 167 (by decide) (by decide)
  · left
    exact rec13278 5 168 (by decide) (by decide)
  · left
    exact rec13278 5 169 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(261,⟨([1],[]),true,([1],[]),false,false,[]⟩),(262,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(263,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(264,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(265,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(306,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(322,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 261)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 262)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13330 5 170 (by decide) (by decide)
      · right
        exact rec13332 5 170 (by decide) (by decide)
      · right
        exact rec13334 5 170 (by decide) (by decide)
      · right
        exact rec13336 5 170 (by decide) (by decide)
      · right
        exact rec13338 5 170 (by decide) (by decide)
      · right
        exact rec13340 5 170 (by decide) (by decide)
      · right
        exact rec13342 5 170 (by decide) (by decide)
      · right
        exact rec13344 5 170 (by decide) (by decide)
      · right
        exact rec13346 5 170 (by decide) (by decide)
      · right
        exact rec13348 5 170 (by decide) (by decide)
      · right
        exact rec13350 5 170 (by decide) (by decide)
      · right
        exact rec13352 5 170 (by decide) (by decide)
      · right
        exact rec13354 5 170 (by decide) (by decide)
      · right
        exact rec13356 5 170 (by decide) (by decide)
      · right
        exact rec13358 5 170 (by decide) (by decide)
      · right
        exact rec13360 5 170 (by decide) (by decide)
      · right
        exact rec13362 5 170 (by decide) (by decide)
      · right
        exact rec13364 5 170 (by decide) (by decide)
      · right
        exact rec13366 5 170 (by decide) (by decide)
      · right
        exact rec13368 5 170 (by decide) (by decide)
      · right
        exact rec13370 5 170 (by decide) (by decide)
      · right
        exact rec13372 5 170 (by decide) (by decide)
      · right
        exact rec13374 5 170 (by decide) (by decide)
      · right
        exact rec13376 5 170 (by decide) (by decide)
      · right
        exact rec13378 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 263)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 264)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13380 5 170 (by decide) (by decide)
      · right
        exact rec13382 5 170 (by decide) (by decide)
      · right
        exact rec13384 5 170 (by decide) (by decide)
      · right
        exact rec13386 5 170 (by decide) (by decide)
      · right
        exact rec13388 5 170 (by decide) (by decide)
      · right
        exact rec13390 5 170 (by decide) (by decide)
      · right
        exact rec13392 5 170 (by decide) (by decide)
      · right
        exact rec13394 5 170 (by decide) (by decide)
      · right
        exact rec13396 5 170 (by decide) (by decide)
      · right
        exact rec13398 5 170 (by decide) (by decide)
      · right
        exact rec13400 5 170 (by decide) (by decide)
      · right
        exact rec13402 5 170 (by decide) (by decide)
      · right
        exact rec13404 5 170 (by decide) (by decide)
      · right
        exact rec13406 5 170 (by decide) (by decide)
      · right
        exact rec13408 5 170 (by decide) (by decide)
      · right
        exact rec13410 5 170 (by decide) (by decide)
      · right
        exact rec13412 5 170 (by decide) (by decide)
      · right
        exact rec13414 5 170 (by decide) (by decide)
      · right
        exact rec13416 5 170 (by decide) (by decide)
      · right
        exact rec13418 5 170 (by decide) (by decide)
      · right
        exact rec13420 5 170 (by decide) (by decide)
      · right
        exact rec13422 5 170 (by decide) (by decide)
      · right
        exact rec13424 5 170 (by decide) (by decide)
      · right
        exact rec13426 5 170 (by decide) (by decide)
      · right
        exact rec13428 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 265)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 266)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 267)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13430 5 170 (by decide) (by decide)
      · right
        exact rec13433 5 170 (by decide) (by decide)
      · right
        exact rec13436 5 170 (by decide) (by decide)
      · right
        exact rec13439 5 170 (by decide) (by decide)
      · right
        exact rec13442 5 170 (by decide) (by decide)
      · right
        exact rec13445 5 170 (by decide) (by decide)
      · right
        exact rec13448 5 170 (by decide) (by decide)
      · right
        exact rec13451 5 170 (by decide) (by decide)
      · right
        exact rec13454 5 170 (by decide) (by decide)
      · right
        exact rec13457 5 170 (by decide) (by decide)
      · right
        exact rec13460 5 170 (by decide) (by decide)
      · right
        exact rec13463 5 170 (by decide) (by decide)
      · right
        exact rec13466 5 170 (by decide) (by decide)
      · right
        exact rec13469 5 170 (by decide) (by decide)
      · right
        exact rec13472 5 170 (by decide) (by decide)
      · right
        exact rec13475 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 268)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 269)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 270)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13478 5 170 (by decide) (by decide)
      · right
        exact rec13481 5 170 (by decide) (by decide)
      · right
        exact rec13484 5 170 (by decide) (by decide)
      · right
        exact rec13487 5 170 (by decide) (by decide)
      · right
        exact rec13490 5 170 (by decide) (by decide)
      · right
        exact rec13493 5 170 (by decide) (by decide)
      · right
        exact rec13496 5 170 (by decide) (by decide)
      · right
        exact rec13499 5 170 (by decide) (by decide)
      · right
        exact rec13502 5 170 (by decide) (by decide)
      · right
        exact rec13505 5 170 (by decide) (by decide)
      · right
        exact rec13508 5 170 (by decide) (by decide)
      · right
        exact rec13511 5 170 (by decide) (by decide)
      · right
        exact rec13514 5 170 (by decide) (by decide)
      · right
        exact rec13517 5 170 (by decide) (by decide)
      · right
        exact rec13520 5 170 (by decide) (by decide)
      · right
        exact rec13523 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 271)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 272)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 273)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13526 5 170 (by decide) (by decide)
      · right
        exact rec13529 5 170 (by decide) (by decide)
      · right
        exact rec13532 5 170 (by decide) (by decide)
      · right
        exact rec13535 5 170 (by decide) (by decide)
      · right
        exact rec13538 5 170 (by decide) (by decide)
      · right
        exact rec13541 5 170 (by decide) (by decide)
      · right
        exact rec13544 5 170 (by decide) (by decide)
      · right
        exact rec13547 5 170 (by decide) (by decide)
      · right
        exact rec13550 5 170 (by decide) (by decide)
      · right
        exact rec13553 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 274)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 275)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13556 5 170 (by decide) (by decide)
      · right
        exact rec13559 5 170 (by decide) (by decide)
      · right
        exact rec13562 5 170 (by decide) (by decide)
      · right
        exact rec13565 5 170 (by decide) (by decide)
      · right
        exact rec13568 5 170 (by decide) (by decide)
      · right
        exact rec13571 5 170 (by decide) (by decide)
      · right
        exact rec13574 5 170 (by decide) (by decide)
      · right
        exact rec13577 5 170 (by decide) (by decide)
      · right
        exact rec13580 5 170 (by decide) (by decide)
      · right
        exact rec13583 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 276)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 277)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 278)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13586 5 170 (by decide) (by decide)
      · right
        exact rec13589 5 170 (by decide) (by decide)
      · right
        exact rec13592 5 170 (by decide) (by decide)
      · right
        exact rec13595 5 170 (by decide) (by decide)
      · right
        exact rec13598 5 170 (by decide) (by decide)
      · right
        exact rec13601 5 170 (by decide) (by decide)
      · right
        exact rec13604 5 170 (by decide) (by decide)
      · right
        exact rec13607 5 170 (by decide) (by decide)
      · right
        exact rec13610 5 170 (by decide) (by decide)
      · right
        exact rec13613 5 170 (by decide) (by decide)
      · right
        exact rec13616 5 170 (by decide) (by decide)
      · right
        exact rec13619 5 170 (by decide) (by decide)
      · right
        exact rec13622 5 170 (by decide) (by decide)
      · right
        exact rec13625 5 170 (by decide) (by decide)
      · right
        exact rec13628 5 170 (by decide) (by decide)
      · right
        exact rec13631 5 170 (by decide) (by decide)
      · right
        exact rec13634 5 170 (by decide) (by decide)
      · right
        exact rec13637 5 170 (by decide) (by decide)
      · right
        exact rec13640 5 170 (by decide) (by decide)
      · right
        exact rec13643 5 170 (by decide) (by decide)
      · right
        exact rec13646 5 170 (by decide) (by decide)
      · right
        exact rec13649 5 170 (by decide) (by decide)
      · right
        exact rec13652 5 170 (by decide) (by decide)
      · right
        exact rec13655 5 170 (by decide) (by decide)
      · right
        exact rec13658 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 279)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 280)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13661 5 170 (by decide) (by decide)
      · right
        exact rec13664 5 170 (by decide) (by decide)
      · right
        exact rec13667 5 170 (by decide) (by decide)
      · right
        exact rec13670 5 170 (by decide) (by decide)
      · right
        exact rec13673 5 170 (by decide) (by decide)
      · right
        exact rec13676 5 170 (by decide) (by decide)
      · right
        exact rec13679 5 170 (by decide) (by decide)
      · right
        exact rec13682 5 170 (by decide) (by decide)
      · right
        exact rec13685 5 170 (by decide) (by decide)
      · right
        exact rec13688 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 281)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 282)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 283)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13691 5 170 (by decide) (by decide)
      · right
        exact rec13694 5 170 (by decide) (by decide)
      · right
        exact rec13697 5 170 (by decide) (by decide)
      · right
        exact rec13700 5 170 (by decide) (by decide)
      · right
        exact rec13703 5 170 (by decide) (by decide)
      · right
        exact rec13706 5 170 (by decide) (by decide)
      · right
        exact rec13709 5 170 (by decide) (by decide)
      · right
        exact rec13712 5 170 (by decide) (by decide)
      · right
        exact rec13715 5 170 (by decide) (by decide)
      · right
        exact rec13718 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 284)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 285)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13721 5 170 (by decide) (by decide)
      · right
        exact rec13724 5 170 (by decide) (by decide)
      · right
        exact rec13727 5 170 (by decide) (by decide)
      · right
        exact rec13730 5 170 (by decide) (by decide)
      · right
        exact rec13733 5 170 (by decide) (by decide)
      · right
        exact rec13736 5 170 (by decide) (by decide)
      · right
        exact rec13739 5 170 (by decide) (by decide)
      · right
        exact rec13742 5 170 (by decide) (by decide)
      · right
        exact rec13745 5 170 (by decide) (by decide)
      · right
        exact rec13748 5 170 (by decide) (by decide)
      · right
        exact rec13751 5 170 (by decide) (by decide)
      · right
        exact rec13754 5 170 (by decide) (by decide)
      · right
        exact rec13757 5 170 (by decide) (by decide)
      · right
        exact rec13760 5 170 (by decide) (by decide)
      · right
        exact rec13763 5 170 (by decide) (by decide)
      · right
        exact rec13766 5 170 (by decide) (by decide)
      · right
        exact rec13769 5 170 (by decide) (by decide)
      · right
        exact rec13772 5 170 (by decide) (by decide)
      · right
        exact rec13775 5 170 (by decide) (by decide)
      · right
        exact rec13778 5 170 (by decide) (by decide)
      · right
        exact rec13781 5 170 (by decide) (by decide)
      · right
        exact rec13784 5 170 (by decide) (by decide)
      · right
        exact rec13787 5 170 (by decide) (by decide)
      · right
        exact rec13790 5 170 (by decide) (by decide)
      · right
        exact rec13793 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 286)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 287)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 288)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13796 5 170 (by decide) (by decide)
      · right
        exact rec13799 5 170 (by decide) (by decide)
      · right
        exact rec13802 5 170 (by decide) (by decide)
      · right
        exact rec13805 5 170 (by decide) (by decide)
      · right
        exact rec13808 5 170 (by decide) (by decide)
      · right
        exact rec13811 5 170 (by decide) (by decide)
      · right
        exact rec13814 5 170 (by decide) (by decide)
      · right
        exact rec13817 5 170 (by decide) (by decide)
      · right
        exact rec13820 5 170 (by decide) (by decide)
      · right
        exact rec13823 5 170 (by decide) (by decide)
      · right
        exact rec13826 5 170 (by decide) (by decide)
      · right
        exact rec13829 5 170 (by decide) (by decide)
      · right
        exact rec13832 5 170 (by decide) (by decide)
      · right
        exact rec13835 5 170 (by decide) (by decide)
      · right
        exact rec13838 5 170 (by decide) (by decide)
      · right
        exact rec13841 5 170 (by decide) (by decide)
      · right
        exact rec13844 5 170 (by decide) (by decide)
      · right
        exact rec13847 5 170 (by decide) (by decide)
      · right
        exact rec13850 5 170 (by decide) (by decide)
      · right
        exact rec13853 5 170 (by decide) (by decide)
      · right
        exact rec13856 5 170 (by decide) (by decide)
      · right
        exact rec13859 5 170 (by decide) (by decide)
      · right
        exact rec13862 5 170 (by decide) (by decide)
      · right
        exact rec13865 5 170 (by decide) (by decide)
      · right
        exact rec13868 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 289)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 290)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13871 5 170 (by decide) (by decide)
      · right
        exact rec13874 5 170 (by decide) (by decide)
      · right
        exact rec13877 5 170 (by decide) (by decide)
      · right
        exact rec13880 5 170 (by decide) (by decide)
      · right
        exact rec13883 5 170 (by decide) (by decide)
      · right
        exact rec13886 5 170 (by decide) (by decide)
      · right
        exact rec13889 5 170 (by decide) (by decide)
      · right
        exact rec13892 5 170 (by decide) (by decide)
      · right
        exact rec13895 5 170 (by decide) (by decide)
      · right
        exact rec13898 5 170 (by decide) (by decide)
      · right
        exact rec13901 5 170 (by decide) (by decide)
      · right
        exact rec13904 5 170 (by decide) (by decide)
      · right
        exact rec13907 5 170 (by decide) (by decide)
      · right
        exact rec13910 5 170 (by decide) (by decide)
      · right
        exact rec13913 5 170 (by decide) (by decide)
      · right
        exact rec13916 5 170 (by decide) (by decide)
      · right
        exact rec13919 5 170 (by decide) (by decide)
      · right
        exact rec13922 5 170 (by decide) (by decide)
      · right
        exact rec13925 5 170 (by decide) (by decide)
      · right
        exact rec13928 5 170 (by decide) (by decide)
      · right
        exact rec13931 5 170 (by decide) (by decide)
      · right
        exact rec13934 5 170 (by decide) (by decide)
      · right
        exact rec13937 5 170 (by decide) (by decide)
      · right
        exact rec13940 5 170 (by decide) (by decide)
      · right
        exact rec13943 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 291)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 292)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 293)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13946 5 170 (by decide) (by decide)
      · right
        exact rec13949 5 170 (by decide) (by decide)
      · right
        exact rec13952 5 170 (by decide) (by decide)
      · right
        exact rec13955 5 170 (by decide) (by decide)
      · right
        exact rec13958 5 170 (by decide) (by decide)
      · right
        exact rec13961 5 170 (by decide) (by decide)
      · right
        exact rec13964 5 170 (by decide) (by decide)
      · right
        exact rec13967 5 170 (by decide) (by decide)
      · right
        exact rec13970 5 170 (by decide) (by decide)
      · right
        exact rec13973 5 170 (by decide) (by decide)
      · right
        exact rec13976 5 170 (by decide) (by decide)
      · right
        exact rec13979 5 170 (by decide) (by decide)
      · right
        exact rec13982 5 170 (by decide) (by decide)
      · right
        exact rec13985 5 170 (by decide) (by decide)
      · right
        exact rec13988 5 170 (by decide) (by decide)
      · right
        exact rec13991 5 170 (by decide) (by decide)
      · right
        exact rec13994 5 170 (by decide) (by decide)
      · right
        exact rec13997 5 170 (by decide) (by decide)
      · right
        exact rec14000 5 170 (by decide) (by decide)
      · right
        exact rec14003 5 170 (by decide) (by decide)
      · right
        exact rec14006 5 170 (by decide) (by decide)
      · right
        exact rec14009 5 170 (by decide) (by decide)
      · right
        exact rec14012 5 170 (by decide) (by decide)
      · right
        exact rec14015 5 170 (by decide) (by decide)
      · right
        exact rec14018 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 294)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 295)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14021 5 170 (by decide) (by decide)
      · right
        exact rec14024 5 170 (by decide) (by decide)
      · right
        exact rec14027 5 170 (by decide) (by decide)
      · right
        exact rec14030 5 170 (by decide) (by decide)
      · right
        exact rec14033 5 170 (by decide) (by decide)
      · right
        exact rec14036 5 170 (by decide) (by decide)
      · right
        exact rec14039 5 170 (by decide) (by decide)
      · right
        exact rec14042 5 170 (by decide) (by decide)
      · right
        exact rec14045 5 170 (by decide) (by decide)
      · right
        exact rec14048 5 170 (by decide) (by decide)
      · right
        exact rec14051 5 170 (by decide) (by decide)
      · right
        exact rec14054 5 170 (by decide) (by decide)
      · right
        exact rec14057 5 170 (by decide) (by decide)
      · right
        exact rec14060 5 170 (by decide) (by decide)
      · right
        exact rec14063 5 170 (by decide) (by decide)
      · right
        exact rec14066 5 170 (by decide) (by decide)
      · right
        exact rec14069 5 170 (by decide) (by decide)
      · right
        exact rec14072 5 170 (by decide) (by decide)
      · right
        exact rec14075 5 170 (by decide) (by decide)
      · right
        exact rec14078 5 170 (by decide) (by decide)
      · right
        exact rec14081 5 170 (by decide) (by decide)
      · right
        exact rec14084 5 170 (by decide) (by decide)
      · right
        exact rec14087 5 170 (by decide) (by decide)
      · right
        exact rec14090 5 170 (by decide) (by decide)
      · right
        exact rec14093 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 296)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 297)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14096 5 170 (by decide) (by decide)
      · right
        exact rec14099 5 170 (by decide) (by decide)
      · right
        exact rec14102 5 170 (by decide) (by decide)
      · right
        exact rec14105 5 170 (by decide) (by decide)
      · right
        exact rec14108 5 170 (by decide) (by decide)
      · right
        exact rec14111 5 170 (by decide) (by decide)
      · right
        exact rec14114 5 170 (by decide) (by decide)
      · right
        exact rec14117 5 170 (by decide) (by decide)
      · right
        exact rec14120 5 170 (by decide) (by decide)
      · right
        exact rec14123 5 170 (by decide) (by decide)
      · right
        exact rec14126 5 170 (by decide) (by decide)
      · right
        exact rec14129 5 170 (by decide) (by decide)
      · right
        exact rec14132 5 170 (by decide) (by decide)
      · right
        exact rec14135 5 170 (by decide) (by decide)
      · right
        exact rec14138 5 170 (by decide) (by decide)
      · right
        exact rec14141 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 298)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 299)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 300)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14144 5 170 (by decide) (by decide)
      · right
        exact rec14147 5 170 (by decide) (by decide)
      · right
        exact rec14150 5 170 (by decide) (by decide)
      · right
        exact rec14153 5 170 (by decide) (by decide)
      · right
        exact rec14156 5 170 (by decide) (by decide)
      · right
        exact rec14159 5 170 (by decide) (by decide)
      · right
        exact rec14162 5 170 (by decide) (by decide)
      · right
        exact rec14165 5 170 (by decide) (by decide)
      · right
        exact rec14168 5 170 (by decide) (by decide)
      · right
        exact rec14171 5 170 (by decide) (by decide)
      · right
        exact rec14174 5 170 (by decide) (by decide)
      · right
        exact rec14177 5 170 (by decide) (by decide)
      · right
        exact rec14180 5 170 (by decide) (by decide)
      · right
        exact rec14183 5 170 (by decide) (by decide)
      · right
        exact rec14186 5 170 (by decide) (by decide)
      · right
        exact rec14189 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 301)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 302)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14192 5 170 (by decide) (by decide)
      · right
        exact rec14195 5 170 (by decide) (by decide)
      · right
        exact rec14198 5 170 (by decide) (by decide)
      · right
        exact rec14201 5 170 (by decide) (by decide)
      · right
        exact rec14204 5 170 (by decide) (by decide)
      · right
        exact rec14207 5 170 (by decide) (by decide)
      · right
        exact rec14210 5 170 (by decide) (by decide)
      · right
        exact rec14213 5 170 (by decide) (by decide)
      · right
        exact rec14216 5 170 (by decide) (by decide)
      · right
        exact rec14219 5 170 (by decide) (by decide)
      · right
        exact rec14222 5 170 (by decide) (by decide)
      · right
        exact rec14225 5 170 (by decide) (by decide)
      · right
        exact rec14228 5 170 (by decide) (by decide)
      · right
        exact rec14231 5 170 (by decide) (by decide)
      · right
        exact rec14234 5 170 (by decide) (by decide)
      · right
        exact rec14237 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 303)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 304)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 305)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14240 5 170 (by decide) (by decide)
      · right
        exact rec14243 5 170 (by decide) (by decide)
      · right
        exact rec14246 5 170 (by decide) (by decide)
      · right
        exact rec14249 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 306)).length = 20 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 307)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14252 5 170 (by decide) (by decide)
      · right
        exact rec14255 5 170 (by decide) (by decide)
      · right
        exact rec14258 5 170 (by decide) (by decide)
      · right
        exact rec14261 5 170 (by decide) (by decide)
      · right
        exact rec14264 5 170 (by decide) (by decide)
      · right
        exact rec14267 5 170 (by decide) (by decide)
      · right
        exact rec14270 5 170 (by decide) (by decide)
      · right
        exact rec14273 5 170 (by decide) (by decide)
      · right
        exact rec14276 5 170 (by decide) (by decide)
      · right
        exact rec14279 5 170 (by decide) (by decide)
      · right
        exact rec14282 5 170 (by decide) (by decide)
      · right
        exact rec14285 5 170 (by decide) (by decide)
      · right
        exact rec14288 5 170 (by decide) (by decide)
      · right
        exact rec14291 5 170 (by decide) (by decide)
      · right
        exact rec14294 5 170 (by decide) (by decide)
      · right
        exact rec14297 5 170 (by decide) (by decide)
      · right
        exact rec14300 5 170 (by decide) (by decide)
      · right
        exact rec14303 5 170 (by decide) (by decide)
      · right
        exact rec14306 5 170 (by decide) (by decide)
      · right
        exact rec14309 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 308)).length = 20 := by decide +kernel
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
      · right
        exact rec14312 5 170 (by decide) (by decide)
      · right
        exact rec14315 5 170 (by decide) (by decide)
      · right
        exact rec14318 5 170 (by decide) (by decide)
      · right
        exact rec14321 5 170 (by decide) (by decide)
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 309)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14324 5 170 (by decide) (by decide)
      · right
        exact rec14327 5 170 (by decide) (by decide)
      · right
        exact rec14330 5 170 (by decide) (by decide)
      · right
        exact rec14333 5 170 (by decide) (by decide)
      · right
        exact rec14336 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 310)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 311)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14339 5 170 (by decide) (by decide)
      · right
        exact rec14342 5 170 (by decide) (by decide)
      · right
        exact rec14345 5 170 (by decide) (by decide)
      · right
        exact rec14348 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 312)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14351 5 170 (by decide) (by decide)
      · right
        exact rec14354 5 170 (by decide) (by decide)
      · right
        exact rec14357 5 170 (by decide) (by decide)
      · right
        exact rec14360 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 313)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14363 5 170 (by decide) (by decide)
      · right
        exact rec14366 5 170 (by decide) (by decide)
      · right
        exact rec14369 5 170 (by decide) (by decide)
      · right
        exact rec14372 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 314)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 315)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14376 5 170 (by decide) (by decide)
      · right
        exact rec14379 5 170 (by decide) (by decide)
      · right
        exact rec14382 5 170 (by decide) (by decide)
      · right
        exact rec14385 5 170 (by decide) (by decide)
      · right
        exact rec14388 5 170 (by decide) (by decide)
      · right
        exact rec14391 5 170 (by decide) (by decide)
      · right
        exact rec14394 5 170 (by decide) (by decide)
      · right
        exact rec14397 5 170 (by decide) (by decide)
      · right
        exact rec14400 5 170 (by decide) (by decide)
      · right
        exact rec14403 5 170 (by decide) (by decide)
      · right
        exact rec14406 5 170 (by decide) (by decide)
      · right
        exact rec14409 5 170 (by decide) (by decide)
      · right
        exact rec14412 5 170 (by decide) (by decide)
      · right
        exact rec14415 5 170 (by decide) (by decide)
      · right
        exact rec14418 5 170 (by decide) (by decide)
      · right
        exact rec14421 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 316)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 317)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14424 5 170 (by decide) (by decide)
      · right
        exact rec14427 5 170 (by decide) (by decide)
      · right
        exact rec14430 5 170 (by decide) (by decide)
      · right
        exact rec14433 5 170 (by decide) (by decide)
      · right
        exact rec14436 5 170 (by decide) (by decide)
      · right
        exact rec14439 5 170 (by decide) (by decide)
      · right
        exact rec14442 5 170 (by decide) (by decide)
      · right
        exact rec14445 5 170 (by decide) (by decide)
      · right
        exact rec14448 5 170 (by decide) (by decide)
      · right
        exact rec14451 5 170 (by decide) (by decide)
      · right
        exact rec14454 5 170 (by decide) (by decide)
      · right
        exact rec14457 5 170 (by decide) (by decide)
      · right
        exact rec14460 5 170 (by decide) (by decide)
      · right
        exact rec14463 5 170 (by decide) (by decide)
      · right
        exact rec14466 5 170 (by decide) (by decide)
      · right
        exact rec14469 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 318)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14472 5 170 (by decide) (by decide)
      · right
        exact rec14475 5 170 (by decide) (by decide)
      · right
        exact rec14478 5 170 (by decide) (by decide)
      · right
        exact rec14481 5 170 (by decide) (by decide)
      · right
        exact rec14484 5 170 (by decide) (by decide)
      · right
        exact rec14487 5 170 (by decide) (by decide)
      · right
        exact rec14490 5 170 (by decide) (by decide)
      · right
        exact rec14493 5 170 (by decide) (by decide)
      · right
        exact rec14496 5 170 (by decide) (by decide)
      · right
        exact rec14499 5 170 (by decide) (by decide)
      · right
        exact rec14502 5 170 (by decide) (by decide)
      · right
        exact rec14505 5 170 (by decide) (by decide)
      · right
        exact rec14508 5 170 (by decide) (by decide)
      · right
        exact rec14511 5 170 (by decide) (by decide)
      · right
        exact rec14514 5 170 (by decide) (by decide)
      · right
        exact rec14517 5 170 (by decide) (by decide)
      · right
        exact rec14520 5 170 (by decide) (by decide)
      · right
        exact rec14523 5 170 (by decide) (by decide)
      · right
        exact rec14526 5 170 (by decide) (by decide)
      · right
        exact rec14529 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 319)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14532 5 170 (by decide) (by decide)
      · right
        exact rec14535 5 170 (by decide) (by decide)
      · right
        exact rec14538 5 170 (by decide) (by decide)
      · right
        exact rec14541 5 170 (by decide) (by decide)
      · right
        exact rec14544 5 170 (by decide) (by decide)
      · right
        exact rec14547 5 170 (by decide) (by decide)
      · right
        exact rec14550 5 170 (by decide) (by decide)
      · right
        exact rec14553 5 170 (by decide) (by decide)
      · right
        exact rec14556 5 170 (by decide) (by decide)
      · right
        exact rec14559 5 170 (by decide) (by decide)
      · right
        exact rec14562 5 170 (by decide) (by decide)
      · right
        exact rec14565 5 170 (by decide) (by decide)
      · right
        exact rec14568 5 170 (by decide) (by decide)
      · right
        exact rec14571 5 170 (by decide) (by decide)
      · right
        exact rec14574 5 170 (by decide) (by decide)
      · right
        exact rec14577 5 170 (by decide) (by decide)
      · right
        exact rec14580 5 170 (by decide) (by decide)
      · right
        exact rec14583 5 170 (by decide) (by decide)
      · right
        exact rec14586 5 170 (by decide) (by decide)
      · right
        exact rec14589 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 320)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 321)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14592 5 170 (by decide) (by decide)
      · right
        exact rec14595 5 170 (by decide) (by decide)
      · right
        exact rec14598 5 170 (by decide) (by decide)
      · right
        exact rec14601 5 170 (by decide) (by decide)
      · right
        exact rec14604 5 170 (by decide) (by decide)
      · right
        exact rec14607 5 170 (by decide) (by decide)
      · right
        exact rec14610 5 170 (by decide) (by decide)
      · right
        exact rec14613 5 170 (by decide) (by decide)
      · right
        exact rec14616 5 170 (by decide) (by decide)
      · right
        exact rec14619 5 170 (by decide) (by decide)
      · right
        exact rec14622 5 170 (by decide) (by decide)
      · right
        exact rec14625 5 170 (by decide) (by decide)
      · right
        exact rec14628 5 170 (by decide) (by decide)
      · right
        exact rec14631 5 170 (by decide) (by decide)
      · right
        exact rec14634 5 170 (by decide) (by decide)
      · right
        exact rec14637 5 170 (by decide) (by decide)
      · right
        exact rec14640 5 170 (by decide) (by decide)
      · right
        exact rec14643 5 170 (by decide) (by decide)
      · right
        exact rec14646 5 170 (by decide) (by decide)
      · right
        exact rec14649 5 170 (by decide) (by decide)
      · right
        exact rec14652 5 170 (by decide) (by decide)
      · right
        exact rec14655 5 170 (by decide) (by decide)
      · right
        exact rec14658 5 170 (by decide) (by decide)
      · right
        exact rec14661 5 170 (by decide) (by decide)
      · right
        exact rec14664 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 322)).length = 20 := by decide +kernel
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
        exact rec14667 5 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec14668 5 170 (by decide) (by decide)
      · right
        exact rec14669 5 170 (by decide) (by decide)
      · right
        exact rec14670 5 170 (by decide) (by decide)
      · left
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
        exact rec14671 5 170 (by decide) (by decide)
      · right
        exact rec14672 5 170 (by decide) (by decide)
      · right
        exact rec14673 5 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec14674 5 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 323)).length = 10 := by decide +kernel
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
    exact rec13285 5 171 (by decide) (by decide)
  · left
    exact rec13278 5 172 (by decide) (by decide)
  · left
    exact rec13278 5 173 (by decide) (by decide)
  · left
    exact rec13287 5 174 (by decide) (by decide)
  · left
    exact rec13285 5 175 (by decide) (by decide)
end Section14Coverage_5_7_p160_176

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0160_0176


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0176_0192
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_7_p176_192
private theorem rec13278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[830]? = some (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec13279 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[831]? = some (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec13285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 151, 171, 175, 187, 191] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[837]? = some (⟨260,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) from rfl))
private theorem rec13288 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[186],909⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[840]? = some (⟨260,(-1),[1,2,5,6,13,14],[186],909⟩) from rfl))
private theorem rec13290 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[842]? = some (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec13291 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,14],[190],909⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[843]? = some (⟨260,(-1),[1,2,5,6,14],[190],909⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0007_parents_0176_0192 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 176).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 7).take 1 = [⟨8,260,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false,[(261,⟨([1],[]),true,([1],[]),false,false,[]⟩),(262,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(263,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(264,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(265,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(306,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(322,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 176).take 16 = [⟨1,176,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,177,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,178,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,179,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,180,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,181,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,182,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,183,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,184,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,185,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,186,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,187,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,188,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,189,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,190,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,191,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec13290 5 176 (by decide) (by decide)
  · left
    exact rec13290 5 177 (by decide) (by decide)
  · left
    exact rec13279 5 178 (by decide) (by decide)
  · left
    exact rec13279 5 179 (by decide) (by decide)
  · left
    exact rec13290 5 180 (by decide) (by decide)
  · left
    exact rec13290 5 181 (by decide) (by decide)
  · left
    exact rec13279 5 182 (by decide) (by decide)
  · left
    exact rec13279 5 183 (by decide) (by decide)
  · left
    exact rec13278 5 184 (by decide) (by decide)
  · left
    exact rec13278 5 185 (by decide) (by decide)
  · left
    exact rec13288 5 186 (by decide) (by decide)
  · left
    exact rec13285 5 187 (by decide) (by decide)
  · left
    exact rec13278 5 188 (by decide) (by decide)
  · left
    exact rec13278 5 189 (by decide) (by decide)
  · left
    exact rec13291 5 190 (by decide) (by decide)
  · left
    exact rec13285 5 191 (by decide) (by decide)
end Section14Coverage_5_7_p176_192

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0176_0192

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
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 128).take 64, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  intro pl hpl
  let xs := section14Parents section14Catalog (section14State section14Catalog 5)
  let P := fun b : Section14Parent => section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j
  exact (all_of_interval_split P xs 128 160 192 (by decide) (by decide) (all_of_interval_split P xs 128 144 160 (by decide) (by decide) (Freiman.workReverse20260919_s0005_coverage0007_parents_0128_0144 pl hpl) (Freiman.workReverse20260919_s0005_coverage0007_parents_0144_0160 pl hpl)) (all_of_interval_split P xs 160 176 192 (by decide) (by decide) (Freiman.workReverse20260919_s0005_coverage0007_parents_0160_0176 pl hpl) (Freiman.workReverse20260919_s0005_coverage0007_parents_0176_0192 pl hpl)))

#print axioms solution
