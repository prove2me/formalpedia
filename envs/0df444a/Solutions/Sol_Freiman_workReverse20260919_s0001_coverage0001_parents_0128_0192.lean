-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_coverage0001_parents_0128_0192
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:46:26.38324+00:00
-- url     : https://prove2.me/submissions/b2eecf01-125f-4d05-b010-40cd524e8d4c

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_coverage0001_parents_0128_0144
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_1_1_p128_144
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec493 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[493]? = some (⟨18,(0),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec496 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,5],[130],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[496]? = some (⟨18,(0),[1,5],[130],73⟩) from rfl))
private theorem rec497 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,5],[134],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[497]? = some (⟨18,(0),[1,5],[134],125⟩) from rfl))
private theorem rec498 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,5,13],[135],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[498]? = some (⟨18,(0),[1,5,13],[135],125⟩) from rfl))
private theorem rec510 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[510]? = some (⟨18,(1),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec513 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,5],[130],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[513]? = some (⟨18,(1),[1,5],[130],73⟩) from rfl))
private theorem rec514 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,5],[134],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[514]? = some (⟨18,(1),[1,5],[134],125⟩) from rfl))
private theorem rec515 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,5,13],[135],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[515]? = some (⟨18,(1),[1,5,13],[135],125⟩) from rfl))
private theorem rec527 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[527]? = some (⟨18,(2),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec530 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,5],[130],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[530]? = some (⟨18,(2),[1,5],[130],73⟩) from rfl))
private theorem rec531 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,5],[134],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[531]? = some (⟨18,(2),[1,5],[134],125⟩) from rfl))
private theorem rec532 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,5,13],[135],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[532]? = some (⟨18,(2),[1,5,13],[135],125⟩) from rfl))
private theorem rec544 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[544]? = some (⟨18,(3),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec547 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,5],[130],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[547]? = some (⟨18,(3),[1,5],[130],73⟩) from rfl))
private theorem rec548 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,5],[134],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[548]? = some (⟨18,(3),[1,5],[134],125⟩) from rfl))
private theorem rec549 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,5,13],[135],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[549]? = some (⟨18,(3),[1,5,13],[135],125⟩) from rfl))
private theorem rec561 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[561]? = some (⟨18,(4),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec564 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,5],[130],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[564]? = some (⟨18,(4),[1,5],[130],73⟩) from rfl))
private theorem rec565 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,5],[134],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[565]? = some (⟨18,(4),[1,5],[134],125⟩) from rfl))
private theorem rec566 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,5,13],[135],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[566]? = some (⟨18,(4),[1,5,13],[135],125⟩) from rfl))
private theorem rec578 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[578]? = some (⟨18,(5),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec581 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,5],[130],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[581]? = some (⟨18,(5),[1,5],[130],74⟩) from rfl))
private theorem rec582 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,5],[134],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[582]? = some (⟨18,(5),[1,5],[134],126⟩) from rfl))
private theorem rec583 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,5,13],[135],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[583]? = some (⟨18,(5),[1,5,13],[135],126⟩) from rfl))
private theorem rec595 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[595]? = some (⟨18,(6),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec598 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,5],[130],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[598]? = some (⟨18,(6),[1,5],[130],74⟩) from rfl))
private theorem rec599 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,5],[134],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[599]? = some (⟨18,(6),[1,5],[134],126⟩) from rfl))
private theorem rec600 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,5,13],[135],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[600]? = some (⟨18,(6),[1,5,13],[135],126⟩) from rfl))
private theorem rec612 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[612]? = some (⟨18,(7),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec615 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,5],[130],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[615]? = some (⟨18,(7),[1,5],[130],74⟩) from rfl))
private theorem rec616 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,5],[134],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[616]? = some (⟨18,(7),[1,5],[134],126⟩) from rfl))
private theorem rec617 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,5,13],[135],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[617]? = some (⟨18,(7),[1,5,13],[135],126⟩) from rfl))
private theorem rec629 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[629]? = some (⟨18,(8),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec632 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,5],[130],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[632]? = some (⟨18,(8),[1,5],[130],74⟩) from rfl))
private theorem rec633 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,5],[134],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[633]? = some (⟨18,(8),[1,5],[134],126⟩) from rfl))
private theorem rec634 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,5,13],[135],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[634]? = some (⟨18,(8),[1,5,13],[135],126⟩) from rfl))
private theorem rec646 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[646]? = some (⟨18,(9),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec649 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,5],[130],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[649]? = some (⟨18,(9),[1,5],[130],74⟩) from rfl))
private theorem rec650 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,5],[134],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[650]? = some (⟨18,(9),[1,5],[134],126⟩) from rfl))
private theorem rec651 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,5,13],[135],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[651]? = some (⟨18,(9),[1,5,13],[135],126⟩) from rfl))
private theorem rec663 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,2,5,6,13,14],[131],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[663]? = some (⟨18,(10),[1,2,5,6,13,14],[131],108⟩) from rfl))
private theorem rec666 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,5],[130],75⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[666]? = some (⟨18,(10),[1,5],[130],75⟩) from rfl))
private theorem rec667 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,5],[134],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[667]? = some (⟨18,(10),[1,5],[134],127⟩) from rfl))
private theorem rec668 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,5,13],[135],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[668]? = some (⟨18,(10),[1,5,13],[135],127⟩) from rfl))
private theorem rec680 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,2,5,6,13,14],[131],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[680]? = some (⟨18,(11),[1,2,5,6,13,14],[131],109⟩) from rfl))
private theorem rec683 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,5],[130],76⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[683]? = some (⟨18,(11),[1,5],[130],76⟩) from rfl))
private theorem rec684 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,5],[134],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[684]? = some (⟨18,(11),[1,5],[134],128⟩) from rfl))
private theorem rec685 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,5,13],[135],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[685]? = some (⟨18,(11),[1,5,13],[135],128⟩) from rfl))
private theorem rec697 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,2,5,6,13,14],[131],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[697]? = some (⟨18,(12),[1,2,5,6,13,14],[131],110⟩) from rfl))
private theorem rec700 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,5],[130],77⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[700]? = some (⟨18,(12),[1,5],[130],77⟩) from rfl))
private theorem rec701 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,5],[134],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[701]? = some (⟨18,(12),[1,5],[134],129⟩) from rfl))
private theorem rec702 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,5,13],[135],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[702]? = some (⟨18,(12),[1,5,13],[135],129⟩) from rfl))
private theorem rec714 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,2,5,6,13,14],[131],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[714]? = some (⟨18,(13),[1,2,5,6,13,14],[131],109⟩) from rfl))
private theorem rec717 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,5],[130],76⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[717]? = some (⟨18,(13),[1,5],[130],76⟩) from rfl))
private theorem rec718 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,5],[134],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[718]? = some (⟨18,(13),[1,5],[134],128⟩) from rfl))
private theorem rec719 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,5,13],[135],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[719]? = some (⟨18,(13),[1,5,13],[135],128⟩) from rfl))
private theorem rec731 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,2,5,6,13,14],[131],111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[731]? = some (⟨18,(14),[1,2,5,6,13,14],[131],111⟩) from rfl))
private theorem rec734 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,5],[130],78⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[734]? = some (⟨18,(14),[1,5],[130],78⟩) from rfl))
private theorem rec735 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,5],[134],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[735]? = some (⟨18,(14),[1,5],[134],130⟩) from rfl))
private theorem rec736 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,5,13],[135],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[736]? = some (⟨18,(14),[1,5,13],[135],130⟩) from rfl))
private theorem rec748 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,2,5,6,13,14],[131],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[748]? = some (⟨18,(15),[1,2,5,6,13,14],[131],108⟩) from rfl))
private theorem rec751 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,5],[130],75⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[751]? = some (⟨18,(15),[1,5],[130],75⟩) from rfl))
private theorem rec752 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,5],[134],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[752]? = some (⟨18,(15),[1,5],[134],127⟩) from rfl))
private theorem rec753 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,5,13],[135],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[753]? = some (⟨18,(15),[1,5,13],[135],127⟩) from rfl))
private theorem rec765 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,2,5,6,13,14],[131],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[765]? = some (⟨18,(16),[1,2,5,6,13,14],[131],112⟩) from rfl))
private theorem rec768 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,5],[130],79⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[768]? = some (⟨18,(16),[1,5],[130],79⟩) from rfl))
private theorem rec769 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,5],[134],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[769]? = some (⟨18,(16),[1,5],[134],131⟩) from rfl))
private theorem rec770 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,5,13],[135],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[770]? = some (⟨18,(16),[1,5,13],[135],131⟩) from rfl))
private theorem rec782 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,2,5,6,13,14],[131],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[782]? = some (⟨18,(17),[1,2,5,6,13,14],[131],112⟩) from rfl))
private theorem rec785 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,5],[130],79⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[785]? = some (⟨18,(17),[1,5],[130],79⟩) from rfl))
private theorem rec786 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,5],[134],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[786]? = some (⟨18,(17),[1,5],[134],131⟩) from rfl))
private theorem rec787 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,5,13],[135],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[787]? = some (⟨18,(17),[1,5,13],[135],131⟩) from rfl))
private theorem rec799 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,2,5,6,13,14],[131],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[799]? = some (⟨18,(18),[1,2,5,6,13,14],[131],112⟩) from rfl))
private theorem rec802 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,5],[130],79⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[802]? = some (⟨18,(18),[1,5],[130],79⟩) from rfl))
private theorem rec803 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,5],[134],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[803]? = some (⟨18,(18),[1,5],[134],131⟩) from rfl))
private theorem rec804 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,5,13],[135],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[804]? = some (⟨18,(18),[1,5,13],[135],131⟩) from rfl))
private theorem rec816 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,2,5,6,13,14],[131],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[816]? = some (⟨18,(19),[1,2,5,6,13,14],[131],112⟩) from rfl))
private theorem rec819 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,5],[130],79⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[819]? = some (⟨18,(19),[1,5],[130],79⟩) from rfl))
private theorem rec820 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,5],[134],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[820]? = some (⟨18,(19),[1,5],[134],131⟩) from rfl))
private theorem rec821 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,5,13],[135],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[821]? = some (⟨18,(19),[1,5,13],[135],131⟩) from rfl))
private theorem rec833 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,2,5,6,13,14],[131],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[833]? = some (⟨18,(20),[1,2,5,6,13,14],[131],108⟩) from rfl))
private theorem rec836 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,5],[130],75⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[836]? = some (⟨18,(20),[1,5],[130],75⟩) from rfl))
private theorem rec837 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,5],[134],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[837]? = some (⟨18,(20),[1,5],[134],127⟩) from rfl))
private theorem rec838 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,5,13],[135],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[838]? = some (⟨18,(20),[1,5,13],[135],127⟩) from rfl))
private theorem rec850 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,2,5,6,13,14],[131],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[850]? = some (⟨18,(21),[1,2,5,6,13,14],[131],109⟩) from rfl))
private theorem rec853 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,5],[130],76⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[853]? = some (⟨18,(21),[1,5],[130],76⟩) from rfl))
private theorem rec854 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,5],[134],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[854]? = some (⟨18,(21),[1,5],[134],128⟩) from rfl))
private theorem rec855 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,5,13],[135],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[855]? = some (⟨18,(21),[1,5,13],[135],128⟩) from rfl))
private theorem rec867 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,2,5,6,13,14],[131],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[867]? = some (⟨18,(22),[1,2,5,6,13,14],[131],110⟩) from rfl))
private theorem rec870 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,5],[130],77⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[870]? = some (⟨18,(22),[1,5],[130],77⟩) from rfl))
private theorem rec871 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,5],[134],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[871]? = some (⟨18,(22),[1,5],[134],129⟩) from rfl))
private theorem rec872 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,5,13],[135],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[872]? = some (⟨18,(22),[1,5,13],[135],129⟩) from rfl))
private theorem rec884 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,2,5,6,13,14],[131],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[884]? = some (⟨18,(23),[1,2,5,6,13,14],[131],109⟩) from rfl))
private theorem rec887 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,5],[130],76⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[887]? = some (⟨18,(23),[1,5],[130],76⟩) from rfl))
private theorem rec888 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,5],[134],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[888]? = some (⟨18,(23),[1,5],[134],128⟩) from rfl))
private theorem rec889 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,5,13],[135],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[889]? = some (⟨18,(23),[1,5,13],[135],128⟩) from rfl))
private theorem rec901 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,2,5,6,13,14],[131],111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[901]? = some (⟨18,(24),[1,2,5,6,13,14],[131],111⟩) from rfl))
private theorem rec904 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,5],[130],78⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[904]? = some (⟨18,(24),[1,5],[130],78⟩) from rfl))
private theorem rec905 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,5],[134],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[905]? = some (⟨18,(24),[1,5],[134],130⟩) from rfl))
private theorem rec906 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,5,13],[135],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[906]? = some (⟨18,(24),[1,5,13],[135],130⟩) from rfl))
private theorem rec918 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[918]? = some (⟨20,(0),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec919 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[919]? = some (⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec922 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[922]? = some (⟨20,(0),[1,5],[134],3⟩) from rfl))
private theorem rec923 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[923]? = some (⟨20,(0),[1,5,13],[135],3⟩) from rfl))
private theorem rec929 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[929]? = some (⟨20,(1),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec930 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[930]? = some (⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec933 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[933]? = some (⟨20,(1),[1,5],[134],3⟩) from rfl))
private theorem rec934 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[934]? = some (⟨20,(1),[1,5,13],[135],3⟩) from rfl))
private theorem rec940 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[940]? = some (⟨20,(2),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec941 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[941]? = some (⟨20,(2),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec944 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[944]? = some (⟨20,(2),[1,5],[134],3⟩) from rfl))
private theorem rec945 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[945]? = some (⟨20,(2),[1,5,13],[135],3⟩) from rfl))
private theorem rec951 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[951]? = some (⟨20,(3),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec952 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[952]? = some (⟨20,(3),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec955 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[955]? = some (⟨20,(3),[1,5],[134],3⟩) from rfl))
private theorem rec956 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[956]? = some (⟨20,(3),[1,5,13],[135],3⟩) from rfl))
private theorem rec962 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[962]? = some (⟨20,(4),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec963 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[963]? = some (⟨20,(4),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec966 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[966]? = some (⟨20,(4),[1,5],[134],3⟩) from rfl))
private theorem rec967 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[967]? = some (⟨20,(4),[1,5,13],[135],3⟩) from rfl))
private theorem rec973 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[973]? = some (⟨20,(5),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec974 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[974]? = some (⟨20,(5),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec977 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[977]? = some (⟨20,(5),[1,5],[134],3⟩) from rfl))
private theorem rec978 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[978]? = some (⟨20,(5),[1,5,13],[135],3⟩) from rfl))
private theorem rec984 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[984]? = some (⟨20,(6),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec985 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[985]? = some (⟨20,(6),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec988 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[988]? = some (⟨20,(6),[1,5],[134],3⟩) from rfl))
private theorem rec989 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[989]? = some (⟨20,(6),[1,5,13],[135],3⟩) from rfl))
private theorem rec995 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[995]? = some (⟨20,(7),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec996 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[996]? = some (⟨20,(7),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec999 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[999]? = some (⟨20,(7),[1,5],[134],3⟩) from rfl))
private theorem rec1000 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1000]? = some (⟨20,(7),[1,5,13],[135],3⟩) from rfl))
private theorem rec1006 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1006]? = some (⟨20,(8),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1007 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1007]? = some (⟨20,(8),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1010 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1010]? = some (⟨20,(8),[1,5],[134],3⟩) from rfl))
private theorem rec1011 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1011]? = some (⟨20,(8),[1,5,13],[135],3⟩) from rfl))
private theorem rec1017 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1017]? = some (⟨20,(9),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1018 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1018]? = some (⟨20,(9),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1021 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1021]? = some (⟨20,(9),[1,5],[134],3⟩) from rfl))
private theorem rec1022 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1022]? = some (⟨20,(9),[1,5,13],[135],3⟩) from rfl))
private theorem rec1028 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1028]? = some (⟨20,(10),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1029 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1029]? = some (⟨20,(10),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1032 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1032]? = some (⟨20,(10),[1,5],[134],3⟩) from rfl))
private theorem rec1033 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1033]? = some (⟨20,(10),[1,5,13],[135],3⟩) from rfl))
private theorem rec1039 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1039]? = some (⟨20,(11),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1040 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1040]? = some (⟨20,(11),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1043 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1043]? = some (⟨20,(11),[1,5],[134],3⟩) from rfl))
private theorem rec1044 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1044]? = some (⟨20,(11),[1,5,13],[135],3⟩) from rfl))
private theorem rec1050 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1050]? = some (⟨20,(12),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1051 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1051]? = some (⟨20,(12),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1054 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1054]? = some (⟨20,(12),[1,5],[134],3⟩) from rfl))
private theorem rec1055 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1055]? = some (⟨20,(12),[1,5,13],[135],3⟩) from rfl))
private theorem rec1061 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1061]? = some (⟨20,(13),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1062 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1062]? = some (⟨20,(13),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1065 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1065]? = some (⟨20,(13),[1,5],[134],3⟩) from rfl))
private theorem rec1066 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1066]? = some (⟨20,(13),[1,5,13],[135],3⟩) from rfl))
private theorem rec1072 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1072]? = some (⟨20,(14),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1073 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1073]? = some (⟨20,(14),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1076 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1076]? = some (⟨20,(14),[1,5],[134],3⟩) from rfl))
private theorem rec1077 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1077]? = some (⟨20,(14),[1,5,13],[135],3⟩) from rfl))
private theorem rec1083 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1083]? = some (⟨20,(15),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1084 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1084]? = some (⟨20,(15),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1087 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1087]? = some (⟨20,(15),[1,5],[134],3⟩) from rfl))
private theorem rec1088 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1088]? = some (⟨20,(15),[1,5,13],[135],3⟩) from rfl))
private theorem rec1094 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1094]? = some (⟨20,(16),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1095 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1095]? = some (⟨20,(16),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1098 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1098]? = some (⟨20,(16),[1,5],[134],3⟩) from rfl))
private theorem rec1099 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1099]? = some (⟨20,(16),[1,5,13],[135],3⟩) from rfl))
private theorem rec1105 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1105]? = some (⟨20,(17),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1106 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1106]? = some (⟨20,(17),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1109 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1109]? = some (⟨20,(17),[1,5],[134],3⟩) from rfl))
private theorem rec1110 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1110]? = some (⟨20,(17),[1,5,13],[135],3⟩) from rfl))
private theorem rec1116 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1116]? = some (⟨20,(18),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1117 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1117]? = some (⟨20,(18),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1120 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1120]? = some (⟨20,(18),[1,5],[134],3⟩) from rfl))
private theorem rec1121 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1121]? = some (⟨20,(18),[1,5,13],[135],3⟩) from rfl))
private theorem rec1127 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1127]? = some (⟨20,(19),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1128 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1128]? = some (⟨20,(19),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1131 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1131]? = some (⟨20,(19),[1,5],[134],3⟩) from rfl))
private theorem rec1132 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1132]? = some (⟨20,(19),[1,5,13],[135],3⟩) from rfl))
private theorem rec1138 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1138]? = some (⟨20,(20),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1139 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1139]? = some (⟨20,(20),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1142 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1142]? = some (⟨20,(20),[1,5],[134],3⟩) from rfl))
private theorem rec1143 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1143]? = some (⟨20,(20),[1,5,13],[135],3⟩) from rfl))
private theorem rec1149 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1149]? = some (⟨20,(21),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1150 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1150]? = some (⟨20,(21),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1153 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1153]? = some (⟨20,(21),[1,5],[134],3⟩) from rfl))
private theorem rec1154 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1154]? = some (⟨20,(21),[1,5,13],[135],3⟩) from rfl))
private theorem rec1160 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1160]? = some (⟨20,(22),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1161 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1161]? = some (⟨20,(22),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1164 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1164]? = some (⟨20,(22),[1,5],[134],3⟩) from rfl))
private theorem rec1165 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1165]? = some (⟨20,(22),[1,5,13],[135],3⟩) from rfl))
private theorem rec1171 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[2]? = some (⟨20,(23),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1172 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[3]? = some (⟨20,(23),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1175 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[6]? = some (⟨20,(23),[1,5],[134],3⟩) from rfl))
private theorem rec1176 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[7]? = some (⟨20,(23),[1,5,13],[135],3⟩) from rfl))
private theorem rec1182 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[13]? = some (⟨20,(24),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1183 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[14]? = some (⟨20,(24),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1186 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[17]? = some (⟨20,(24),[1,5],[134],3⟩) from rfl))
private theorem rec1187 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[18]? = some (⟨20,(24),[1,5,13],[135],3⟩) from rfl))
private theorem rec1193 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[24]? = some (⟨23,(0),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1194 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[25]? = some (⟨23,(0),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1196 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[27]? = some (⟨23,(0),[1,5],[134],2⟩) from rfl))
private theorem rec1197 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[28]? = some (⟨23,(0),[1,5,13],[135],2⟩) from rfl))
private theorem rec1200 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[31]? = some (⟨23,(1),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1201 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[32]? = some (⟨23,(1),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1203 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[34]? = some (⟨23,(1),[1,5],[134],2⟩) from rfl))
private theorem rec1204 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[35]? = some (⟨23,(1),[1,5,13],[135],2⟩) from rfl))
private theorem rec1207 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[38]? = some (⟨23,(2),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1208 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[39]? = some (⟨23,(2),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1210 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[41]? = some (⟨23,(2),[1,5],[134],2⟩) from rfl))
private theorem rec1211 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[42]? = some (⟨23,(2),[1,5,13],[135],2⟩) from rfl))
private theorem rec1214 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[45]? = some (⟨23,(3),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1215 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[46]? = some (⟨23,(3),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1217 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[48]? = some (⟨23,(3),[1,5],[134],2⟩) from rfl))
private theorem rec1218 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[49]? = some (⟨23,(3),[1,5,13],[135],2⟩) from rfl))
private theorem rec1221 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[52]? = some (⟨23,(4),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1222 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[53]? = some (⟨23,(4),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1224 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[55]? = some (⟨23,(4),[1,5],[134],2⟩) from rfl))
private theorem rec1225 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[56]? = some (⟨23,(4),[1,5,13],[135],2⟩) from rfl))
private theorem rec1228 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[59]? = some (⟨23,(5),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1229 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[60]? = some (⟨23,(5),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1231 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[62]? = some (⟨23,(5),[1,5],[134],2⟩) from rfl))
private theorem rec1232 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[63]? = some (⟨23,(5),[1,5,13],[135],2⟩) from rfl))
private theorem rec1235 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[66]? = some (⟨23,(6),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1236 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[67]? = some (⟨23,(6),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1238 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[69]? = some (⟨23,(6),[1,5],[134],2⟩) from rfl))
private theorem rec1239 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[70]? = some (⟨23,(6),[1,5,13],[135],2⟩) from rfl))
private theorem rec1242 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[73]? = some (⟨23,(7),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1243 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[74]? = some (⟨23,(7),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1245 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[76]? = some (⟨23,(7),[1,5],[134],2⟩) from rfl))
private theorem rec1246 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[77]? = some (⟨23,(7),[1,5,13],[135],2⟩) from rfl))
private theorem rec1249 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[80]? = some (⟨23,(8),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1250 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[81]? = some (⟨23,(8),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1252 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[83]? = some (⟨23,(8),[1,5],[134],2⟩) from rfl))
private theorem rec1253 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[84]? = some (⟨23,(8),[1,5,13],[135],2⟩) from rfl))
private theorem rec1256 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[87]? = some (⟨23,(9),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1257 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[88]? = some (⟨23,(9),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1259 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[90]? = some (⟨23,(9),[1,5],[134],2⟩) from rfl))
private theorem rec1260 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[91]? = some (⟨23,(9),[1,5,13],[135],2⟩) from rfl))
private theorem rec1263 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[94]? = some (⟨23,(10),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1264 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[95]? = some (⟨23,(10),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1266 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[97]? = some (⟨23,(10),[1,5],[134],2⟩) from rfl))
private theorem rec1267 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[98]? = some (⟨23,(10),[1,5,13],[135],2⟩) from rfl))
private theorem rec1270 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[101]? = some (⟨23,(11),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1271 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[102]? = some (⟨23,(11),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1273 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[104]? = some (⟨23,(11),[1,5],[134],2⟩) from rfl))
private theorem rec1274 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[105]? = some (⟨23,(11),[1,5,13],[135],2⟩) from rfl))
private theorem rec1277 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[108]? = some (⟨23,(12),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[109]? = some (⟨23,(12),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1280 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[111]? = some (⟨23,(12),[1,5],[134],2⟩) from rfl))
private theorem rec1281 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[112]? = some (⟨23,(12),[1,5,13],[135],2⟩) from rfl))
private theorem rec1284 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[115]? = some (⟨23,(13),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[116]? = some (⟨23,(13),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1287 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[118]? = some (⟨23,(13),[1,5],[134],2⟩) from rfl))
private theorem rec1288 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[119]? = some (⟨23,(13),[1,5,13],[135],2⟩) from rfl))
private theorem rec1291 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[122]? = some (⟨23,(14),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1292 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[123]? = some (⟨23,(14),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1294 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[125]? = some (⟨23,(14),[1,5],[134],2⟩) from rfl))
private theorem rec1295 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[126]? = some (⟨23,(14),[1,5,13],[135],2⟩) from rfl))
private theorem rec1298 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[129]? = some (⟨23,(15),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1299 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[130]? = some (⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1301 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[132]? = some (⟨23,(15),[1,5],[134],2⟩) from rfl))
private theorem rec1302 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[133]? = some (⟨23,(15),[1,5,13],[135],2⟩) from rfl))
private theorem rec1305 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[136]? = some (⟨23,(16),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1306 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[137]? = some (⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1308 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[139]? = some (⟨23,(16),[1,5],[134],2⟩) from rfl))
private theorem rec1309 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[140]? = some (⟨23,(16),[1,5,13],[135],2⟩) from rfl))
private theorem rec1312 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[143]? = some (⟨23,(17),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1313 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[144]? = some (⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1315 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[146]? = some (⟨23,(17),[1,5],[134],2⟩) from rfl))
private theorem rec1316 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[147]? = some (⟨23,(17),[1,5,13],[135],2⟩) from rfl))
private theorem rec1319 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[150]? = some (⟨23,(18),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1320 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[151]? = some (⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1322 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[153]? = some (⟨23,(18),[1,5],[134],2⟩) from rfl))
private theorem rec1323 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[154]? = some (⟨23,(18),[1,5,13],[135],2⟩) from rfl))
private theorem rec1326 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[157]? = some (⟨23,(19),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1327 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[158]? = some (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1329 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[160]? = some (⟨23,(19),[1,5],[134],2⟩) from rfl))
private theorem rec1330 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[161]? = some (⟨23,(19),[1,5,13],[135],2⟩) from rfl))
private theorem rec1333 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[164]? = some (⟨23,(20),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1334 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[165]? = some (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1336 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[167]? = some (⟨23,(20),[1,5],[134],2⟩) from rfl))
private theorem rec1337 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[168]? = some (⟨23,(20),[1,5,13],[135],2⟩) from rfl))
private theorem rec1340 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[171]? = some (⟨23,(21),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[172]? = some (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1343 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[174]? = some (⟨23,(21),[1,5],[134],2⟩) from rfl))
private theorem rec1344 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[175]? = some (⟨23,(21),[1,5,13],[135],2⟩) from rfl))
private theorem rec1347 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[178]? = some (⟨23,(22),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1348 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[179]? = some (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1350 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[181]? = some (⟨23,(22),[1,5],[134],2⟩) from rfl))
private theorem rec1351 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[182]? = some (⟨23,(22),[1,5,13],[135],2⟩) from rfl))
private theorem rec1354 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[185]? = some (⟨23,(23),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1355 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[186]? = some (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1357 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[188]? = some (⟨23,(23),[1,5],[134],2⟩) from rfl))
private theorem rec1358 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[189]? = some (⟨23,(23),[1,5,13],[135],2⟩) from rfl))
private theorem rec1361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[192]? = some (⟨23,(24),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[193]? = some (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1364 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[195]? = some (⟨23,(24),[1,5],[134],2⟩) from rfl))
private theorem rec1365 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[196]? = some (⟨23,(24),[1,5,13],[135],2⟩) from rfl))
private theorem rec1368 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,2,5,6],[130],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[199]? = some (⟨25,(0),[1,2,5,6],[130],80⟩) from rfl))
private theorem rec1371 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,2,13,14],[131],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[202]? = some (⟨25,(0),[1,2,13,14],[131],80⟩) from rfl))
private theorem rec1374 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,5],[134],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[205]? = some (⟨25,(0),[1,5],[134],80⟩) from rfl))
private theorem rec1375 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,13],[135],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[206]? = some (⟨25,(0),[1,13],[135],80⟩) from rfl))
private theorem rec1389 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,2,5,6],[130],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[220]? = some (⟨25,(1),[1,2,5,6],[130],81⟩) from rfl))
private theorem rec1391 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,2,13,14],[131],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[222]? = some (⟨25,(1),[1,2,13,14],[131],81⟩) from rfl))
private theorem rec1395 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,5],[134],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[226]? = some (⟨25,(1),[1,5],[134],81⟩) from rfl))
private theorem rec1396 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,13],[135],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[227]? = some (⟨25,(1),[1,13],[135],81⟩) from rfl))
private theorem rec1413 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,2,5,6],[130],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[244]? = some (⟨25,(2),[1,2,5,6],[130],80⟩) from rfl))
private theorem rec1415 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,2,13,14],[131],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[246]? = some (⟨25,(2),[1,2,13,14],[131],80⟩) from rfl))
private theorem rec1419 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,5],[134],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[250]? = some (⟨25,(2),[1,5],[134],80⟩) from rfl))
private theorem rec1420 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,13],[135],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[251]? = some (⟨25,(2),[1,13],[135],80⟩) from rfl))
private theorem rec1437 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,2,5,6],[130],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[268]? = some (⟨25,(3),[1,2,5,6],[130],82⟩) from rfl))
private theorem rec1439 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,2,13,14],[131],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[270]? = some (⟨25,(3),[1,2,13,14],[131],82⟩) from rfl))
private theorem rec1443 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,5],[134],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[274]? = some (⟨25,(3),[1,5],[134],82⟩) from rfl))
private theorem rec1444 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,13],[135],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[275]? = some (⟨25,(3),[1,13],[135],82⟩) from rfl))
private theorem rec1461 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,2,5,6],[130],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[292]? = some (⟨25,(4),[1,2,5,6],[130],83⟩) from rfl))
private theorem rec1463 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,2,13,14],[131],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[294]? = some (⟨25,(4),[1,2,13,14],[131],83⟩) from rfl))
private theorem rec1467 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,5],[134],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[298]? = some (⟨25,(4),[1,5],[134],83⟩) from rfl))
private theorem rec1468 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,13],[135],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[299]? = some (⟨25,(4),[1,13],[135],83⟩) from rfl))
private theorem rec1485 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,2,5,6],[130],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[316]? = some (⟨25,(5),[1,2,5,6],[130],80⟩) from rfl))
private theorem rec1488 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,2,13,14],[131],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[319]? = some (⟨25,(5),[1,2,13,14],[131],80⟩) from rfl))
private theorem rec1491 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,5],[134],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[322]? = some (⟨25,(5),[1,5],[134],80⟩) from rfl))
private theorem rec1492 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,13],[135],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[323]? = some (⟨25,(5),[1,13],[135],80⟩) from rfl))
private theorem rec1506 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,2,5,6],[130],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[337]? = some (⟨25,(6),[1,2,5,6],[130],81⟩) from rfl))
private theorem rec1508 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,2,13,14],[131],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[339]? = some (⟨25,(6),[1,2,13,14],[131],81⟩) from rfl))
private theorem rec1512 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,5],[134],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[343]? = some (⟨25,(6),[1,5],[134],81⟩) from rfl))
private theorem rec1513 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,13],[135],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[344]? = some (⟨25,(6),[1,13],[135],81⟩) from rfl))
private theorem rec1530 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,2,5,6],[130],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[361]? = some (⟨25,(7),[1,2,5,6],[130],80⟩) from rfl))
private theorem rec1532 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,2,13,14],[131],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[363]? = some (⟨25,(7),[1,2,13,14],[131],80⟩) from rfl))
private theorem rec1536 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,5],[134],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[367]? = some (⟨25,(7),[1,5],[134],80⟩) from rfl))
private theorem rec1537 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,13],[135],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[368]? = some (⟨25,(7),[1,13],[135],80⟩) from rfl))
private theorem rec1554 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,2,5,6],[130],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[385]? = some (⟨25,(8),[1,2,5,6],[130],82⟩) from rfl))
private theorem rec1556 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,2,13,14],[131],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[387]? = some (⟨25,(8),[1,2,13,14],[131],82⟩) from rfl))
private theorem rec1560 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,5],[134],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[391]? = some (⟨25,(8),[1,5],[134],82⟩) from rfl))
private theorem rec1561 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,13],[135],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[392]? = some (⟨25,(8),[1,13],[135],82⟩) from rfl))
private theorem rec1578 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,2,5,6],[130],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[409]? = some (⟨25,(9),[1,2,5,6],[130],83⟩) from rfl))
private theorem rec1580 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,2,13,14],[131],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[411]? = some (⟨25,(9),[1,2,13,14],[131],83⟩) from rfl))
private theorem rec1584 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,5],[134],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[415]? = some (⟨25,(9),[1,5],[134],83⟩) from rfl))
private theorem rec1585 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,13],[135],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[416]? = some (⟨25,(9),[1,13],[135],83⟩) from rfl))
private theorem rec1602 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,2,5,6],[130],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[433]? = some (⟨25,(10),[1,2,5,6],[130],84⟩) from rfl))
private theorem rec1605 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,2,13,14],[131],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[436]? = some (⟨25,(10),[1,2,13,14],[131],84⟩) from rfl))
private theorem rec1608 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,5],[134],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[439]? = some (⟨25,(10),[1,5],[134],84⟩) from rfl))
private theorem rec1609 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,13],[135],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[440]? = some (⟨25,(10),[1,13],[135],84⟩) from rfl))
private theorem rec1623 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,2,5,6],[130],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[454]? = some (⟨25,(11),[1,2,5,6],[130],84⟩) from rfl))
private theorem rec1625 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,2,13,14],[131],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[456]? = some (⟨25,(11),[1,2,13,14],[131],84⟩) from rfl))
private theorem rec1629 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,5],[134],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[460]? = some (⟨25,(11),[1,5],[134],84⟩) from rfl))
private theorem rec1630 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,13],[135],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[461]? = some (⟨25,(11),[1,13],[135],84⟩) from rfl))
private theorem rec1647 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,2,5,6],[130],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[478]? = some (⟨25,(12),[1,2,5,6],[130],84⟩) from rfl))
private theorem rec1649 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,2,13,14],[131],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[480]? = some (⟨25,(12),[1,2,13,14],[131],84⟩) from rfl))
private theorem rec1653 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,5],[134],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[484]? = some (⟨25,(12),[1,5],[134],84⟩) from rfl))
private theorem rec1654 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,13],[135],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[485]? = some (⟨25,(12),[1,13],[135],84⟩) from rfl))
private theorem rec1671 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,2,5,6],[130],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[502]? = some (⟨25,(13),[1,2,5,6],[130],84⟩) from rfl))
private theorem rec1673 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,2,13,14],[131],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[504]? = some (⟨25,(13),[1,2,13,14],[131],84⟩) from rfl))
private theorem rec1677 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,5],[134],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[508]? = some (⟨25,(13),[1,5],[134],84⟩) from rfl))
private theorem rec1678 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,13],[135],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[509]? = some (⟨25,(13),[1,13],[135],84⟩) from rfl))
private theorem rec1695 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,2,5,6],[130],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[526]? = some (⟨25,(14),[1,2,5,6],[130],83⟩) from rfl))
private theorem rec1697 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,2,13,14],[131],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[528]? = some (⟨25,(14),[1,2,13,14],[131],83⟩) from rfl))
private theorem rec1701 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,5],[134],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[532]? = some (⟨25,(14),[1,5],[134],83⟩) from rfl))
private theorem rec1702 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,13],[135],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[533]? = some (⟨25,(14),[1,13],[135],83⟩) from rfl))
private theorem rec1719 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[550]? = some (⟨25,(15),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1722 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,2,13,14],[131],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[553]? = some (⟨25,(15),[1,2,13,14],[131],35⟩) from rfl))
private theorem rec1725 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,5],[134],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[556]? = some (⟨25,(15),[1,5],[134],35⟩) from rfl))
private theorem rec1726 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,13],[135],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[557]? = some (⟨25,(15),[1,13],[135],35⟩) from rfl))
private theorem rec1740 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[571]? = some (⟨25,(16),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1742 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,2,13,14],[131],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[573]? = some (⟨25,(16),[1,2,13,14],[131],35⟩) from rfl))
private theorem rec1746 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,5],[134],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[577]? = some (⟨25,(16),[1,5],[134],35⟩) from rfl))
private theorem rec1747 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,13],[135],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[578]? = some (⟨25,(16),[1,13],[135],35⟩) from rfl))
private theorem rec1764 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[595]? = some (⟨25,(17),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1766 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,2,13,14],[131],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[597]? = some (⟨25,(17),[1,2,13,14],[131],35⟩) from rfl))
private theorem rec1770 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,5],[134],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[601]? = some (⟨25,(17),[1,5],[134],35⟩) from rfl))
private theorem rec1771 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,13],[135],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[602]? = some (⟨25,(17),[1,13],[135],35⟩) from rfl))
private theorem rec1788 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[619]? = some (⟨25,(18),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1790 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,2,13,14],[131],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[621]? = some (⟨25,(18),[1,2,13,14],[131],35⟩) from rfl))
private theorem rec1794 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,5],[134],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[625]? = some (⟨25,(18),[1,5],[134],35⟩) from rfl))
private theorem rec1795 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,13],[135],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[626]? = some (⟨25,(18),[1,13],[135],35⟩) from rfl))
private theorem rec1812 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[643]? = some (⟨25,(19),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1814 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,2,13,14],[131],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[645]? = some (⟨25,(19),[1,2,13,14],[131],35⟩) from rfl))
private theorem rec1818 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,5],[134],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[649]? = some (⟨25,(19),[1,5],[134],35⟩) from rfl))
private theorem rec1819 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,13],[135],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[650]? = some (⟨25,(19),[1,13],[135],35⟩) from rfl))
private theorem rec1836 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[667]? = some (⟨25,(20),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1839 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,2,13,14],[131],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[670]? = some (⟨25,(20),[1,2,13,14],[131],38⟩) from rfl))
private theorem rec1842 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,5],[134],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[673]? = some (⟨25,(20),[1,5],[134],38⟩) from rfl))
private theorem rec1843 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,13],[135],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[674]? = some (⟨25,(20),[1,13],[135],38⟩) from rfl))
private theorem rec1857 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[688]? = some (⟨25,(21),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1859 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,2,13,14],[131],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[690]? = some (⟨25,(21),[1,2,13,14],[131],38⟩) from rfl))
private theorem rec1863 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,5],[134],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[694]? = some (⟨25,(21),[1,5],[134],38⟩) from rfl))
private theorem rec1864 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,13],[135],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[695]? = some (⟨25,(21),[1,13],[135],38⟩) from rfl))
private theorem rec1881 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[712]? = some (⟨25,(22),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1883 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,2,13,14],[131],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[714]? = some (⟨25,(22),[1,2,13,14],[131],38⟩) from rfl))
private theorem rec1887 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,5],[134],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[718]? = some (⟨25,(22),[1,5],[134],38⟩) from rfl))
private theorem rec1888 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,13],[135],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[719]? = some (⟨25,(22),[1,13],[135],38⟩) from rfl))
private theorem rec1905 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[736]? = some (⟨25,(23),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1907 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,2,13,14],[131],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[738]? = some (⟨25,(23),[1,2,13,14],[131],38⟩) from rfl))
private theorem rec1911 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,5],[134],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[742]? = some (⟨25,(23),[1,5],[134],38⟩) from rfl))
private theorem rec1912 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,13],[135],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[743]? = some (⟨25,(23),[1,13],[135],38⟩) from rfl))
private theorem rec1929 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[760]? = some (⟨25,(24),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1931 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,2,13,14],[131],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[762]? = some (⟨25,(24),[1,2,13,14],[131],38⟩) from rfl))
private theorem rec1935 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,5],[134],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[766]? = some (⟨25,(24),[1,5],[134],38⟩) from rfl))
private theorem rec1936 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,13],[135],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[767]? = some (⟨25,(24),[1,13],[135],38⟩) from rfl))
private theorem rec1957 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[788]? = some (⟨28,(0),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec1959 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1,5],[130],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[790]? = some (⟨28,(0),[1,5],[130],85⟩) from rfl))
private theorem rec1960 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1,5],[134,135],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[791]? = some (⟨28,(0),[1,5],[134,135],132⟩) from rfl))
private theorem rec1973 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[804]? = some (⟨28,(1),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec1975 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1,5],[130],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[806]? = some (⟨28,(1),[1,5],[130],85⟩) from rfl))
private theorem rec1976 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1,5],[134,135],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[807]? = some (⟨28,(1),[1,5],[134,135],132⟩) from rfl))
private theorem rec1989 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[820]? = some (⟨28,(2),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec1991 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1,5],[130],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[822]? = some (⟨28,(2),[1,5],[130],85⟩) from rfl))
private theorem rec1992 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1,5],[134,135],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[823]? = some (⟨28,(2),[1,5],[134,135],132⟩) from rfl))
private theorem rec2005 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[836]? = some (⟨28,(3),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec2007 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1,5],[130],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[838]? = some (⟨28,(3),[1,5],[130],85⟩) from rfl))
private theorem rec2008 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1,5],[134,135],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[839]? = some (⟨28,(3),[1,5],[134,135],132⟩) from rfl))
private theorem rec2021 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[852]? = some (⟨28,(4),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec2023 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1,5],[130],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[854]? = some (⟨28,(4),[1,5],[130],85⟩) from rfl))
private theorem rec2024 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1,5],[134,135],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[855]? = some (⟨28,(4),[1,5],[134,135],132⟩) from rfl))
private theorem rec2037 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[868]? = some (⟨28,(5),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2039 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1,5],[130],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[870]? = some (⟨28,(5),[1,5],[130],86⟩) from rfl))
private theorem rec2040 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1,5],[134,135],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[871]? = some (⟨28,(5),[1,5],[134,135],133⟩) from rfl))
private theorem rec2053 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[884]? = some (⟨28,(6),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2055 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1,5],[130],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[886]? = some (⟨28,(6),[1,5],[130],86⟩) from rfl))
private theorem rec2056 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1,5],[134,135],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[887]? = some (⟨28,(6),[1,5],[134,135],133⟩) from rfl))
private theorem rec2069 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[900]? = some (⟨28,(7),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2071 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1,5],[130],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[902]? = some (⟨28,(7),[1,5],[130],86⟩) from rfl))
private theorem rec2072 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1,5],[134,135],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[903]? = some (⟨28,(7),[1,5],[134,135],133⟩) from rfl))
private theorem rec2085 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[916]? = some (⟨28,(8),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2087 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1,5],[130],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[918]? = some (⟨28,(8),[1,5],[130],86⟩) from rfl))
private theorem rec2088 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1,5],[134,135],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[919]? = some (⟨28,(8),[1,5],[134,135],133⟩) from rfl))
private theorem rec2101 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[932]? = some (⟨28,(9),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2103 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1,5],[130],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[934]? = some (⟨28,(9),[1,5],[130],86⟩) from rfl))
private theorem rec2104 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1,5],[134,135],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[935]? = some (⟨28,(9),[1,5],[134,135],133⟩) from rfl))
private theorem rec2117 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1,2,5,6],[131],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[948]? = some (⟨28,(10),[1,2,5,6],[131],115⟩) from rfl))
private theorem rec2119 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1,5],[130],87⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[950]? = some (⟨28,(10),[1,5],[130],87⟩) from rfl))
private theorem rec2120 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1,5],[134,135],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[951]? = some (⟨28,(10),[1,5],[134,135],134⟩) from rfl))
private theorem rec2133 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1,2,5,6],[131],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[964]? = some (⟨28,(11),[1,2,5,6],[131],116⟩) from rfl))
private theorem rec2135 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1,5],[130],88⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[966]? = some (⟨28,(11),[1,5],[130],88⟩) from rfl))
private theorem rec2136 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1,5],[134,135],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[967]? = some (⟨28,(11),[1,5],[134,135],135⟩) from rfl))
private theorem rec2149 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1,2,5,6],[131],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[980]? = some (⟨28,(12),[1,2,5,6],[131],117⟩) from rfl))
private theorem rec2151 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1,5],[130],89⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[982]? = some (⟨28,(12),[1,5],[130],89⟩) from rfl))
private theorem rec2152 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1,5],[134,135],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[983]? = some (⟨28,(12),[1,5],[134,135],136⟩) from rfl))
private theorem rec2165 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1,2,5,6],[131],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[996]? = some (⟨28,(13),[1,2,5,6],[131],116⟩) from rfl))
private theorem rec2167 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1,5],[130],88⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[998]? = some (⟨28,(13),[1,5],[130],88⟩) from rfl))
private theorem rec2168 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1,5],[134,135],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[999]? = some (⟨28,(13),[1,5],[134,135],135⟩) from rfl))
private theorem rec2181 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1,2,5,6],[131],118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1012]? = some (⟨28,(14),[1,2,5,6],[131],118⟩) from rfl))
private theorem rec2183 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1,5],[130],90⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1014]? = some (⟨28,(14),[1,5],[130],90⟩) from rfl))
private theorem rec2184 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1,5],[134,135],137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1015]? = some (⟨28,(14),[1,5],[134,135],137⟩) from rfl))
private theorem rec2197 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1,2,5,6],[131],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1028]? = some (⟨28,(15),[1,2,5,6],[131],115⟩) from rfl))
private theorem rec2199 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1,5],[130],87⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1030]? = some (⟨28,(15),[1,5],[130],87⟩) from rfl))
private theorem rec2200 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1,5],[134,135],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1031]? = some (⟨28,(15),[1,5],[134,135],134⟩) from rfl))
private theorem rec2213 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1,2,5,6],[131],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1044]? = some (⟨28,(16),[1,2,5,6],[131],119⟩) from rfl))
private theorem rec2215 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1,5],[130],91⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1046]? = some (⟨28,(16),[1,5],[130],91⟩) from rfl))
private theorem rec2216 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1,5],[134,135],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1047]? = some (⟨28,(16),[1,5],[134,135],138⟩) from rfl))
private theorem rec2229 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1,2,5,6],[131],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1060]? = some (⟨28,(17),[1,2,5,6],[131],119⟩) from rfl))
private theorem rec2231 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1,5],[130],91⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1062]? = some (⟨28,(17),[1,5],[130],91⟩) from rfl))
private theorem rec2232 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1,5],[134,135],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1063]? = some (⟨28,(17),[1,5],[134,135],138⟩) from rfl))
private theorem rec2245 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1,2,5,6],[131],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1076]? = some (⟨28,(18),[1,2,5,6],[131],119⟩) from rfl))
private theorem rec2247 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1,5],[130],91⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1078]? = some (⟨28,(18),[1,5],[130],91⟩) from rfl))
private theorem rec2248 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1,5],[134,135],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1079]? = some (⟨28,(18),[1,5],[134,135],138⟩) from rfl))
private theorem rec2261 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1,2,5,6],[131],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1092]? = some (⟨28,(19),[1,2,5,6],[131],119⟩) from rfl))
private theorem rec2263 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1,5],[130],91⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1094]? = some (⟨28,(19),[1,5],[130],91⟩) from rfl))
private theorem rec2264 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1,5],[134,135],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1095]? = some (⟨28,(19),[1,5],[134,135],138⟩) from rfl))
private theorem rec2277 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1,2,5,6],[131],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1108]? = some (⟨28,(20),[1,2,5,6],[131],115⟩) from rfl))
private theorem rec2279 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1,5],[130],87⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1110]? = some (⟨28,(20),[1,5],[130],87⟩) from rfl))
private theorem rec2280 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1,5],[134,135],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1111]? = some (⟨28,(20),[1,5],[134,135],134⟩) from rfl))
private theorem rec2293 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1,2,5,6],[131],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1124]? = some (⟨28,(21),[1,2,5,6],[131],116⟩) from rfl))
private theorem rec2295 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1,5],[130],88⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1126]? = some (⟨28,(21),[1,5],[130],88⟩) from rfl))
private theorem rec2296 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1,5],[134,135],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1127]? = some (⟨28,(21),[1,5],[134,135],135⟩) from rfl))
private theorem rec2309 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1,2,5,6],[131],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1140]? = some (⟨28,(22),[1,2,5,6],[131],117⟩) from rfl))
private theorem rec2311 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1,5],[130],89⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1142]? = some (⟨28,(22),[1,5],[130],89⟩) from rfl))
private theorem rec2312 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1,5],[134,135],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1143]? = some (⟨28,(22),[1,5],[134,135],136⟩) from rfl))
private theorem rec2325 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1,2,5,6],[131],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1156]? = some (⟨28,(23),[1,2,5,6],[131],116⟩) from rfl))
private theorem rec2327 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1,5],[130],88⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1158]? = some (⟨28,(23),[1,5],[130],88⟩) from rfl))
private theorem rec2328 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1,5],[134,135],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1159]? = some (⟨28,(23),[1,5],[134,135],135⟩) from rfl))
private theorem rec2341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1,2,5,6],[131],118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1172]? = some (⟨28,(24),[1,2,5,6],[131],118⟩) from rfl))
private theorem rec2343 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1,5],[130],90⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1174]? = some (⟨28,(24),[1,5],[130],90⟩) from rfl))
private theorem rec2344 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1,5],[134,135],137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1175]? = some (⟨28,(24),[1,5],[134,135],137⟩) from rfl))
private theorem rec2353 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[1],[134],92⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1184]? = some (⟨30,(0),[1],[134],92⟩) from rfl))
private theorem rec2354 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([135, 151] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[1],[135,151],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1185]? = some (⟨30,(0),[1],[135,151],120⟩) from rfl))
private theorem rec2355 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[1,2],[130],92⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1186]? = some (⟨30,(0),[1,2],[130],92⟩) from rfl))
private theorem rec2359 (si parent : ℕ) (hs : si ∈ ([1, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[1,6],[131],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1190]? = some (⟨30,(0),[1,6],[131],120⟩) from rfl))
private theorem rec2369 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[1],[134,135],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1200]? = some (⟨30,(1),[1],[134,135],93⟩) from rfl))
private theorem rec2371 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([130, 131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[1,2],[130,131],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1202]? = some (⟨30,(1),[1,2],[130,131],93⟩) from rfl))
private theorem rec2387 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,2,5,6],[130],92⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1218]? = some (⟨30,(2),[1,2,5,6],[130],92⟩) from rfl))
private theorem rec2390 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,5],[134],92⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1221]? = some (⟨30,(2),[1,5],[134],92⟩) from rfl))
private theorem rec2391 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,5],[135],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1222]? = some (⟨30,(2),[1,5],[135],120⟩) from rfl))
private theorem rec2392 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,5,6],[131],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1223]? = some (⟨30,(2),[1,5,6],[131],120⟩) from rfl))
private theorem rec2404 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1],[135],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1235]? = some (⟨30,(3),[1],[135],93⟩) from rfl))
private theorem rec2406 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1,2],[131],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1237]? = some (⟨30,(3),[1,2],[131],93⟩) from rfl))
private theorem rec2410 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1,2,5,6],[130],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1241]? = some (⟨30,(3),[1,2,5,6],[130],93⟩) from rfl))
private theorem rec2412 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1,5],[134],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1243]? = some (⟨30,(3),[1,5],[134],93⟩) from rfl))
private theorem rec2428 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1],[135],94⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1259]? = some (⟨30,(4),[1],[135],94⟩) from rfl))
private theorem rec2430 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1,2],[131],94⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1261]? = some (⟨30,(4),[1,2],[131],94⟩) from rfl))
private theorem rec2434 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1,2,5,6],[130],94⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1265]? = some (⟨30,(4),[1,2,5,6],[130],94⟩) from rfl))
private theorem rec2436 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1,5],[134],94⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1267]? = some (⟨30,(4),[1,5],[134],94⟩) from rfl))
private theorem rec2452 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1],[135],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[9]? = some (⟨30,(5),[1],[135],93⟩) from rfl))
private theorem rec2454 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1,2],[131],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[11]? = some (⟨30,(5),[1,2],[131],93⟩) from rfl))
private theorem rec2458 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1,2,5,6],[130],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[15]? = some (⟨30,(5),[1,2,5,6],[130],93⟩) from rfl))
private theorem rec2460 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1,5],[134],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[17]? = some (⟨30,(5),[1,5],[134],93⟩) from rfl))
private theorem rec2476 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1],[135],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[33]? = some (⟨30,(6),[1],[135],95⟩) from rfl))
private theorem rec2478 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1,2],[131],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[35]? = some (⟨30,(6),[1,2],[131],95⟩) from rfl))
private theorem rec2482 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1,2,5,6],[130],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[39]? = some (⟨30,(6),[1,2,5,6],[130],95⟩) from rfl))
private theorem rec2484 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1,5],[134],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[41]? = some (⟨30,(6),[1,5],[134],95⟩) from rfl))
private theorem rec2500 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1],[135],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[57]? = some (⟨30,(7),[1],[135],95⟩) from rfl))
private theorem rec2502 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1,2],[131],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[59]? = some (⟨30,(7),[1,2],[131],95⟩) from rfl))
private theorem rec2506 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1,2,5,6],[130],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[63]? = some (⟨30,(7),[1,2,5,6],[130],95⟩) from rfl))
private theorem rec2508 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1,5],[134],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[65]? = some (⟨30,(7),[1,5],[134],95⟩) from rfl))
private theorem rec2524 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1],[135],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[81]? = some (⟨30,(8),[1],[135],96⟩) from rfl))
private theorem rec2526 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1,2],[131],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[83]? = some (⟨30,(8),[1,2],[131],96⟩) from rfl))
private theorem rec2530 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1,2,5,6],[130],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[87]? = some (⟨30,(8),[1,2,5,6],[130],96⟩) from rfl))
private theorem rec2532 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1,5],[134],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[89]? = some (⟨30,(8),[1,5],[134],96⟩) from rfl))
private theorem rec2548 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1],[135],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[105]? = some (⟨30,(9),[1],[135],96⟩) from rfl))
private theorem rec2550 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1,2],[131],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[107]? = some (⟨30,(9),[1,2],[131],96⟩) from rfl))
private theorem rec2554 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1,2,5,6],[130],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[111]? = some (⟨30,(9),[1,2,5,6],[130],96⟩) from rfl))
private theorem rec2556 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1,5],[134],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[113]? = some (⟨30,(9),[1,5],[134],96⟩) from rfl))
private theorem rec2573 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[1,2,5,6],[130],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[130]? = some (⟨33,(0),[1,2,5,6],[130],97⟩) from rfl))
private theorem rec2574 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[1,2,5,6,14],[131],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[131]? = some (⟨33,(0),[1,2,5,6,14],[131],97⟩) from rfl))
private theorem rec2575 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[1,5],[134,135],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[132]? = some (⟨33,(0),[1,5],[134,135],97⟩) from rfl))
private theorem rec2584 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(1),[1,5],[134,135],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[141]? = some (⟨33,(1),[1,5],[134,135],98⟩) from rfl))
private theorem rec2585 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(1),[1,5,6],[130,131],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[142]? = some (⟨33,(1),[1,5,6],[130,131],98⟩) from rfl))
private theorem rec2597 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130, 131, 134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(2),[1,5],[130,131,134,135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[154]? = some (⟨33,(2),[1,5],[130,131,134,135],3⟩) from rfl))
private theorem rec2610 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[167]? = some (⟨33,(3),[1,5],[134],3⟩) from rfl))
private theorem rec2611 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[168]? = some (⟨33,(3),[1,5,6],[130],3⟩) from rfl))
private theorem rec2612 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[169]? = some (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2613 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[170]? = some (⟨33,(3),[1,5,13],[135],3⟩) from rfl))
private theorem rec2621 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[178]? = some (⟨33,(4),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec2622 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,2,5,6,13,14],[131],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[179]? = some (⟨33,(4),[1,2,5,6,13,14],[131],2⟩) from rfl))
private theorem rec2623 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[180]? = some (⟨33,(4),[1,5],[134],2⟩) from rfl))
private theorem rec2625 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[182]? = some (⟨33,(4),[1,5,13],[135],2⟩) from rfl))
private theorem rec2635 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[1,5],[134,135],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[192]? = some (⟨33,(5),[1,5],[134,135],98⟩) from rfl))
private theorem rec2636 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[1,5,6],[130,131],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[193]? = some (⟨33,(5),[1,5,6],[130,131],98⟩) from rfl))
private theorem rec2646 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[203]? = some (⟨33,(6),[1,5],[134],3⟩) from rfl))
private theorem rec2647 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[204]? = some (⟨33,(6),[1,5,6],[130],3⟩) from rfl))
private theorem rec2648 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[205]? = some (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2649 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[206]? = some (⟨33,(6),[1,5,13],[135],3⟩) from rfl))
private theorem rec2657 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[214]? = some (⟨33,(7),[1,5],[134],3⟩) from rfl))
private theorem rec2658 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[215]? = some (⟨33,(7),[1,5,6],[130],3⟩) from rfl))
private theorem rec2659 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[216]? = some (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2660 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[217]? = some (⟨33,(7),[1,5,13],[135],3⟩) from rfl))
private theorem rec2666 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,2,5,6],[130],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[223]? = some (⟨33,(8),[1,2,5,6],[130],97⟩) from rfl))
private theorem rec2667 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,2,5,6,13,14],[131],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[224]? = some (⟨33,(8),[1,2,5,6,13,14],[131],97⟩) from rfl))
private theorem rec2671 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,5],[134],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[228]? = some (⟨33,(8),[1,5],[134],97⟩) from rfl))
private theorem rec2672 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,5,13],[135],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[229]? = some (⟨33,(8),[1,5,13],[135],97⟩) from rfl))
private theorem rec2676 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,2,5,6],[130],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[233]? = some (⟨33,(9),[1,2,5,6],[130],98⟩) from rfl))
private theorem rec2677 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,2,5,6,13,14],[131],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[234]? = some (⟨33,(9),[1,2,5,6,13,14],[131],98⟩) from rfl))
private theorem rec2681 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,5],[134],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[238]? = some (⟨33,(9),[1,5],[134],98⟩) from rfl))
private theorem rec2682 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,5,13],[135],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[239]? = some (⟨33,(9),[1,5,13],[135],98⟩) from rfl))
private theorem rec2686 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[1],[134,135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[243]? = some (⟨33,(10),[1],[134,135],3⟩) from rfl))
private theorem rec2687 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([130, 131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[1,2],[130,131],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[244]? = some (⟨33,(10),[1,2],[130,131],3⟩) from rfl))
private theorem rec2697 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[254]? = some (⟨33,(11),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec2698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[255]? = some (⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2701 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[258]? = some (⟨33,(11),[1,5],[134],3⟩) from rfl))
private theorem rec2702 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[259]? = some (⟨33,(11),[1,5,13],[135],3⟩) from rfl))
private theorem rec2707 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,2,5,6],[130,146,150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[264]? = some (⟨33,(12),[1,2,5,6],[130,146,150],99⟩) from rfl))
private theorem rec2708 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,2,5,6,13,14],[131],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[265]? = some (⟨33,(12),[1,2,5,6,13,14],[131],99⟩) from rfl))
private theorem rec2710 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,5],[134],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[267]? = some (⟨33,(12),[1,5],[134],99⟩) from rfl))
private theorem rec2711 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,5,13],[135],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[268]? = some (⟨33,(12),[1,5,13],[135],99⟩) from rfl))
private theorem rec2718 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(13),[1,2,5,6],[130,131],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[275]? = some (⟨33,(13),[1,2,5,6],[130,131],99⟩) from rfl))
private theorem rec2722 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(13),[1,5],[134,135],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[279]? = some (⟨33,(13),[1,5],[134,135],99⟩) from rfl))
private theorem rec2731 (si parent : ℕ) (hs : si ∈ ([1, 2, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[1,2,5],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[288]? = some (⟨33,(14),[1,2,5],[130],3⟩) from rfl))
private theorem rec2732 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[1,2,5,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[289]? = some (⟨33,(14),[1,2,5,14],[131,146,150],3⟩) from rfl))
private theorem rec2735 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[1,5],[134,135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[292]? = some (⟨33,(14),[1,5],[134,135],3⟩) from rfl))
private theorem rec2742 (si parent : ℕ) (hs : si ∈ ([1, 2, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[1,2,5],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[299]? = some (⟨33,(15),[1,2,5],[130],3⟩) from rfl))
private theorem rec2743 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[1,2,5,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[300]? = some (⟨33,(15),[1,2,5,14],[131,146,150],3⟩) from rfl))
private theorem rec2746 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[1,5],[134,135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[303]? = some (⟨33,(15),[1,5],[134,135],3⟩) from rfl))
private theorem rec2753 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[310]? = some (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2754 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(0),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[311]? = some (⟨35,(0),[1,5],[134,135],2⟩) from rfl))
private theorem rec2758 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[315]? = some (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2759 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(1),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[316]? = some (⟨35,(1),[1,5],[134,135],2⟩) from rfl))
private theorem rec2765 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,2,5,6],[131],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[322]? = some (⟨35,(2),[1,2,5,6],[131],101⟩) from rfl))
private theorem rec2767 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,5],[130],100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[324]? = some (⟨35,(2),[1,5],[130],100⟩) from rfl))
private theorem rec2768 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,5],[135],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[325]? = some (⟨35,(2),[1,5],[135],101⟩) from rfl))
private theorem rec2769 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,5],[134],139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[326]? = some (⟨35,(2),[1,5],[134],139⟩) from rfl))
private theorem rec2781 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[338]? = some (⟨35,(3),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2782 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,2,5,6],[131],121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[339]? = some (⟨35,(3),[1,2,5,6],[131],121⟩) from rfl))
private theorem rec2783 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,5],[134],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[340]? = some (⟨35,(3),[1,5],[134],101⟩) from rfl))
private theorem rec2784 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,5],[135],139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[341]? = some (⟨35,(3),[1,5],[135],139⟩) from rfl))
private theorem rec2790 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[347]? = some (⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2791 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(4),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[348]? = some (⟨35,(4),[1,5],[134,135],2⟩) from rfl))
private theorem rec2795 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[352]? = some (⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2796 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(5),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[353]? = some (⟨35,(5),[1,5],[134,135],2⟩) from rfl))
private theorem rec2802 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,2,5,6],[131],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[359]? = some (⟨35,(6),[1,2,5,6],[131],101⟩) from rfl))
private theorem rec2804 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,5],[135],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[361]? = some (⟨35,(6),[1,5],[135],101⟩) from rfl))
private theorem rec2805 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,5],[130],102⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[362]? = some (⟨35,(6),[1,5],[130],102⟩) from rfl))
private theorem rec2806 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,5],[134],140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[363]? = some (⟨35,(6),[1,5],[134],140⟩) from rfl))
private theorem rec2818 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[375]? = some (⟨35,(7),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2819 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,2,5,6],[131],122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[376]? = some (⟨35,(7),[1,2,5,6],[131],122⟩) from rfl))
private theorem rec2820 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,5],[134],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[377]? = some (⟨35,(7),[1,5],[134],101⟩) from rfl))
private theorem rec2821 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,5],[135],140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[378]? = some (⟨35,(7),[1,5],[135],140⟩) from rfl))
private theorem rec2827 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[384]? = some (⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2828 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(8),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[385]? = some (⟨35,(8),[1,5],[134,135],2⟩) from rfl))
private theorem rec2832 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[389]? = some (⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2833 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(9),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[390]? = some (⟨35,(9),[1,5],[134,135],2⟩) from rfl))
private theorem rec2839 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,2,5,6],[131],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[396]? = some (⟨35,(10),[1,2,5,6],[131],101⟩) from rfl))
private theorem rec2841 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,5],[135],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[398]? = some (⟨35,(10),[1,5],[135],101⟩) from rfl))
private theorem rec2842 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,5],[130],103⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[399]? = some (⟨35,(10),[1,5],[130],103⟩) from rfl))
private theorem rec2843 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,5],[134],141⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[400]? = some (⟨35,(10),[1,5],[134],141⟩) from rfl))
private theorem rec2855 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[412]? = some (⟨35,(11),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2856 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,2,5,6],[131],123⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[413]? = some (⟨35,(11),[1,2,5,6],[131],123⟩) from rfl))
private theorem rec2857 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,5],[134],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[414]? = some (⟨35,(11),[1,5],[134],101⟩) from rfl))
private theorem rec2858 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,5],[135],144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[415]? = some (⟨35,(11),[1,5],[135],144⟩) from rfl))
private theorem rec2864 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(12),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[421]? = some (⟨35,(12),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2865 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(12),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[422]? = some (⟨35,(12),[1,5],[134,135],2⟩) from rfl))
private theorem rec2869 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(13),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[426]? = some (⟨35,(13),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2870 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(13),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[427]? = some (⟨35,(13),[1,5],[134,135],2⟩) from rfl))
private theorem rec2876 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,2,5,6],[131],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[433]? = some (⟨35,(14),[1,2,5,6],[131],101⟩) from rfl))
private theorem rec2878 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,5],[135],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[435]? = some (⟨35,(14),[1,5],[135],101⟩) from rfl))
private theorem rec2879 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,5],[130],104⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[436]? = some (⟨35,(14),[1,5],[130],104⟩) from rfl))
private theorem rec2880 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,5],[134],142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[437]? = some (⟨35,(14),[1,5],[134],142⟩) from rfl))
private theorem rec2892 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[449]? = some (⟨35,(15),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2893 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,2,5,6],[131],124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[450]? = some (⟨35,(15),[1,2,5,6],[131],124⟩) from rfl))
private theorem rec2894 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,5],[134],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[451]? = some (⟨35,(15),[1,5],[134],101⟩) from rfl))
private theorem rec2895 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,5],[135],142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[452]? = some (⟨35,(15),[1,5],[135],142⟩) from rfl))
private theorem rec2899 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,2,5,6],[130],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[456]? = some (⟨36,(5),[1,2,5,6],[130],105⟩) from rfl))
private theorem rec2900 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[457]? = some (⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩) from rfl))
private theorem rec2903 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,5],[134],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[460]? = some (⟨36,(5),[1,5],[134],105⟩) from rfl))
private theorem rec2904 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,5,13],[135],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[461]? = some (⟨36,(5),[1,5,13],[135],105⟩) from rfl))
private theorem rec2909 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[466]? = some (⟨36,(7),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec2911 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,2,5,6,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[468]? = some (⟨36,(7),[1,2,5,6,14],[131,146],3⟩) from rfl))
private theorem rec2913 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[470]? = some (⟨36,(7),[1,5],[134],3⟩) from rfl))
private theorem rec2914 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[471]? = some (⟨36,(7),[1,5,13],[135],3⟩) from rfl))
private theorem rec2923 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[480]? = some (⟨36,(8),[1,5],[134],3⟩) from rfl))
private theorem rec2924 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[481]? = some (⟨36,(8),[1,5,6],[130],3⟩) from rfl))
private theorem rec2925 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[482]? = some (⟨36,(8),[1,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2926 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[483]? = some (⟨36,(8),[1,5,13],[135],3⟩) from rfl))
private theorem rec2933 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[1],[130],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[490]? = some (⟨36,(9),[1],[130],105⟩) from rfl))
private theorem rec2936 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[1,5],[134],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[493]? = some (⟨36,(9),[1,5],[134],143⟩) from rfl))
private theorem rec2937 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[1,5,13],[135],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[494]? = some (⟨36,(9),[1,5,13],[135],143⟩) from rfl))
private theorem rec2938 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([131, 146, 147] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[1,13],[131,146,147],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[495]? = some (⟨36,(9),[1,13],[131,146,147],105⟩) from rfl))
private theorem rec2949 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[506]? = some (⟨36,(15),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec2950 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1,2,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[507]? = some (⟨36,(15),[1,2,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2953 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1,5],[134,135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[510]? = some (⟨36,(15),[1,5],[134,135],3⟩) from rfl))
private theorem rec2960 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[517]? = some (⟨36,(16),[1,5],[134],3⟩) from rfl))
private theorem rec2961 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[518]? = some (⟨36,(16),[1,5,6],[130],3⟩) from rfl))
private theorem rec2962 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[519]? = some (⟨36,(16),[1,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2963 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[520]? = some (⟨36,(16),[1,5,13],[135],3⟩) from rfl))
private theorem rec2970 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([134, 135, 151] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[1],[134,135,151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[527]? = some (⟨36,(17),[1],[134,135,151],3⟩) from rfl))
private theorem rec2971 (si parent : ℕ) (hs : si ∈ ([1, 2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[1,2,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[528]? = some (⟨36,(17),[1,2,6],[130],3⟩) from rfl))
private theorem rec2972 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[1,2,6,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[529]? = some (⟨36,(17),[1,2,6,14],[131,146,150],3⟩) from rfl))
private theorem rec2981 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([134, 135, 151] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[1],[134,135,151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[538]? = some (⟨36,(19),[1],[134,135,151],3⟩) from rfl))
private theorem rec2982 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 147, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[1,2],[130,131,146,147,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[539]? = some (⟨36,(19),[1,2],[130,131,146,147,150],3⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0001_coverage0001_parents_0128_0144 : ∀ pl ∈ ((section14State section14Catalog 1).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 128).take 16, section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 1).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 128).take 16 = [⟨1,128,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,129,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,130,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,131,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,132,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,133,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,134,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,135,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,136,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,137,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,138,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,139,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,140,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,141,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,142,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,143,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec361 1 128 (by decide) (by decide)
  · left
    exact rec361 1 129 (by decide) (by decide)
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
        exact rec496 1 130 (by decide) (by decide)
      · right
        exact rec513 1 130 (by decide) (by decide)
      · right
        exact rec530 1 130 (by decide) (by decide)
      · right
        exact rec547 1 130 (by decide) (by decide)
      · right
        exact rec564 1 130 (by decide) (by decide)
      · right
        exact rec581 1 130 (by decide) (by decide)
      · right
        exact rec598 1 130 (by decide) (by decide)
      · right
        exact rec615 1 130 (by decide) (by decide)
      · right
        exact rec632 1 130 (by decide) (by decide)
      · right
        exact rec649 1 130 (by decide) (by decide)
      · right
        exact rec666 1 130 (by decide) (by decide)
      · right
        exact rec683 1 130 (by decide) (by decide)
      · right
        exact rec700 1 130 (by decide) (by decide)
      · right
        exact rec717 1 130 (by decide) (by decide)
      · right
        exact rec734 1 130 (by decide) (by decide)
      · right
        exact rec751 1 130 (by decide) (by decide)
      · right
        exact rec768 1 130 (by decide) (by decide)
      · right
        exact rec785 1 130 (by decide) (by decide)
      · right
        exact rec802 1 130 (by decide) (by decide)
      · right
        exact rec819 1 130 (by decide) (by decide)
      · right
        exact rec836 1 130 (by decide) (by decide)
      · right
        exact rec853 1 130 (by decide) (by decide)
      · right
        exact rec870 1 130 (by decide) (by decide)
      · right
        exact rec887 1 130 (by decide) (by decide)
      · right
        exact rec904 1 130 (by decide) (by decide)
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
        exact rec918 1 130 (by decide) (by decide)
      · right
        exact rec929 1 130 (by decide) (by decide)
      · right
        exact rec940 1 130 (by decide) (by decide)
      · right
        exact rec951 1 130 (by decide) (by decide)
      · right
        exact rec962 1 130 (by decide) (by decide)
      · right
        exact rec973 1 130 (by decide) (by decide)
      · right
        exact rec984 1 130 (by decide) (by decide)
      · right
        exact rec995 1 130 (by decide) (by decide)
      · right
        exact rec1006 1 130 (by decide) (by decide)
      · right
        exact rec1017 1 130 (by decide) (by decide)
      · right
        exact rec1028 1 130 (by decide) (by decide)
      · right
        exact rec1039 1 130 (by decide) (by decide)
      · right
        exact rec1050 1 130 (by decide) (by decide)
      · right
        exact rec1061 1 130 (by decide) (by decide)
      · right
        exact rec1072 1 130 (by decide) (by decide)
      · right
        exact rec1083 1 130 (by decide) (by decide)
      · right
        exact rec1094 1 130 (by decide) (by decide)
      · right
        exact rec1105 1 130 (by decide) (by decide)
      · right
        exact rec1116 1 130 (by decide) (by decide)
      · right
        exact rec1127 1 130 (by decide) (by decide)
      · right
        exact rec1138 1 130 (by decide) (by decide)
      · right
        exact rec1149 1 130 (by decide) (by decide)
      · right
        exact rec1160 1 130 (by decide) (by decide)
      · right
        exact rec1171 1 130 (by decide) (by decide)
      · right
        exact rec1182 1 130 (by decide) (by decide)
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
        exact rec1193 1 130 (by decide) (by decide)
      · right
        exact rec1200 1 130 (by decide) (by decide)
      · right
        exact rec1207 1 130 (by decide) (by decide)
      · right
        exact rec1214 1 130 (by decide) (by decide)
      · right
        exact rec1221 1 130 (by decide) (by decide)
      · right
        exact rec1228 1 130 (by decide) (by decide)
      · right
        exact rec1235 1 130 (by decide) (by decide)
      · right
        exact rec1242 1 130 (by decide) (by decide)
      · right
        exact rec1249 1 130 (by decide) (by decide)
      · right
        exact rec1256 1 130 (by decide) (by decide)
      · right
        exact rec1263 1 130 (by decide) (by decide)
      · right
        exact rec1270 1 130 (by decide) (by decide)
      · right
        exact rec1277 1 130 (by decide) (by decide)
      · right
        exact rec1284 1 130 (by decide) (by decide)
      · right
        exact rec1291 1 130 (by decide) (by decide)
      · right
        exact rec1298 1 130 (by decide) (by decide)
      · right
        exact rec1305 1 130 (by decide) (by decide)
      · right
        exact rec1312 1 130 (by decide) (by decide)
      · right
        exact rec1319 1 130 (by decide) (by decide)
      · right
        exact rec1326 1 130 (by decide) (by decide)
      · right
        exact rec1333 1 130 (by decide) (by decide)
      · right
        exact rec1340 1 130 (by decide) (by decide)
      · right
        exact rec1347 1 130 (by decide) (by decide)
      · right
        exact rec1354 1 130 (by decide) (by decide)
      · right
        exact rec1361 1 130 (by decide) (by decide)
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
        exact rec1368 1 130 (by decide) (by decide)
      · right
        exact rec1389 1 130 (by decide) (by decide)
      · right
        exact rec1413 1 130 (by decide) (by decide)
      · right
        exact rec1437 1 130 (by decide) (by decide)
      · right
        exact rec1461 1 130 (by decide) (by decide)
      · right
        exact rec1485 1 130 (by decide) (by decide)
      · right
        exact rec1506 1 130 (by decide) (by decide)
      · right
        exact rec1530 1 130 (by decide) (by decide)
      · right
        exact rec1554 1 130 (by decide) (by decide)
      · right
        exact rec1578 1 130 (by decide) (by decide)
      · right
        exact rec1602 1 130 (by decide) (by decide)
      · right
        exact rec1623 1 130 (by decide) (by decide)
      · right
        exact rec1647 1 130 (by decide) (by decide)
      · right
        exact rec1671 1 130 (by decide) (by decide)
      · right
        exact rec1695 1 130 (by decide) (by decide)
      · right
        exact rec1719 1 130 (by decide) (by decide)
      · right
        exact rec1740 1 130 (by decide) (by decide)
      · right
        exact rec1764 1 130 (by decide) (by decide)
      · right
        exact rec1788 1 130 (by decide) (by decide)
      · right
        exact rec1812 1 130 (by decide) (by decide)
      · right
        exact rec1836 1 130 (by decide) (by decide)
      · right
        exact rec1857 1 130 (by decide) (by decide)
      · right
        exact rec1881 1 130 (by decide) (by decide)
      · right
        exact rec1905 1 130 (by decide) (by decide)
      · right
        exact rec1929 1 130 (by decide) (by decide)
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
        exact rec1959 1 130 (by decide) (by decide)
      · right
        exact rec1975 1 130 (by decide) (by decide)
      · right
        exact rec1991 1 130 (by decide) (by decide)
      · right
        exact rec2007 1 130 (by decide) (by decide)
      · right
        exact rec2023 1 130 (by decide) (by decide)
      · right
        exact rec2039 1 130 (by decide) (by decide)
      · right
        exact rec2055 1 130 (by decide) (by decide)
      · right
        exact rec2071 1 130 (by decide) (by decide)
      · right
        exact rec2087 1 130 (by decide) (by decide)
      · right
        exact rec2103 1 130 (by decide) (by decide)
      · right
        exact rec2119 1 130 (by decide) (by decide)
      · right
        exact rec2135 1 130 (by decide) (by decide)
      · right
        exact rec2151 1 130 (by decide) (by decide)
      · right
        exact rec2167 1 130 (by decide) (by decide)
      · right
        exact rec2183 1 130 (by decide) (by decide)
      · right
        exact rec2199 1 130 (by decide) (by decide)
      · right
        exact rec2215 1 130 (by decide) (by decide)
      · right
        exact rec2231 1 130 (by decide) (by decide)
      · right
        exact rec2247 1 130 (by decide) (by decide)
      · right
        exact rec2263 1 130 (by decide) (by decide)
      · right
        exact rec2279 1 130 (by decide) (by decide)
      · right
        exact rec2295 1 130 (by decide) (by decide)
      · right
        exact rec2311 1 130 (by decide) (by decide)
      · right
        exact rec2327 1 130 (by decide) (by decide)
      · right
        exact rec2343 1 130 (by decide) (by decide)
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
        exact rec2355 1 130 (by decide) (by decide)
      · right
        exact rec2371 1 130 (by decide) (by decide)
      · right
        exact rec2387 1 130 (by decide) (by decide)
      · right
        exact rec2410 1 130 (by decide) (by decide)
      · right
        exact rec2434 1 130 (by decide) (by decide)
      · right
        exact rec2458 1 130 (by decide) (by decide)
      · right
        exact rec2482 1 130 (by decide) (by decide)
      · right
        exact rec2506 1 130 (by decide) (by decide)
      · right
        exact rec2530 1 130 (by decide) (by decide)
      · right
        exact rec2554 1 130 (by decide) (by decide)
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
        exact rec2573 1 130 (by decide) (by decide)
      · right
        exact rec2585 1 130 (by decide) (by decide)
      · right
        exact rec2597 1 130 (by decide) (by decide)
      · right
        exact rec2611 1 130 (by decide) (by decide)
      · right
        exact rec2621 1 130 (by decide) (by decide)
      · right
        exact rec2636 1 130 (by decide) (by decide)
      · right
        exact rec2647 1 130 (by decide) (by decide)
      · right
        exact rec2658 1 130 (by decide) (by decide)
      · right
        exact rec2666 1 130 (by decide) (by decide)
      · right
        exact rec2676 1 130 (by decide) (by decide)
      · right
        exact rec2687 1 130 (by decide) (by decide)
      · right
        exact rec2697 1 130 (by decide) (by decide)
      · right
        exact rec2707 1 130 (by decide) (by decide)
      · right
        exact rec2718 1 130 (by decide) (by decide)
      · right
        exact rec2731 1 130 (by decide) (by decide)
      · right
        exact rec2742 1 130 (by decide) (by decide)
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
        exact rec2753 1 130 (by decide) (by decide)
      · right
        exact rec2758 1 130 (by decide) (by decide)
      · right
        exact rec2767 1 130 (by decide) (by decide)
      · right
        exact rec2781 1 130 (by decide) (by decide)
      · right
        exact rec2790 1 130 (by decide) (by decide)
      · right
        exact rec2795 1 130 (by decide) (by decide)
      · right
        exact rec2805 1 130 (by decide) (by decide)
      · right
        exact rec2818 1 130 (by decide) (by decide)
      · right
        exact rec2827 1 130 (by decide) (by decide)
      · right
        exact rec2832 1 130 (by decide) (by decide)
      · right
        exact rec2842 1 130 (by decide) (by decide)
      · right
        exact rec2855 1 130 (by decide) (by decide)
      · right
        exact rec2864 1 130 (by decide) (by decide)
      · right
        exact rec2869 1 130 (by decide) (by decide)
      · right
        exact rec2879 1 130 (by decide) (by decide)
      · right
        exact rec2892 1 130 (by decide) (by decide)
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
        exact rec2899 1 130 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2909 1 130 (by decide) (by decide)
      · right
        exact rec2924 1 130 (by decide) (by decide)
      · right
        exact rec2933 1 130 (by decide) (by decide)
      · left
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
        exact rec2949 1 130 (by decide) (by decide)
      · right
        exact rec2961 1 130 (by decide) (by decide)
      · right
        exact rec2971 1 130 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2982 1 130 (by decide) (by decide)
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
        exact rec493 1 131 (by decide) (by decide)
      · right
        exact rec510 1 131 (by decide) (by decide)
      · right
        exact rec527 1 131 (by decide) (by decide)
      · right
        exact rec544 1 131 (by decide) (by decide)
      · right
        exact rec561 1 131 (by decide) (by decide)
      · right
        exact rec578 1 131 (by decide) (by decide)
      · right
        exact rec595 1 131 (by decide) (by decide)
      · right
        exact rec612 1 131 (by decide) (by decide)
      · right
        exact rec629 1 131 (by decide) (by decide)
      · right
        exact rec646 1 131 (by decide) (by decide)
      · right
        exact rec663 1 131 (by decide) (by decide)
      · right
        exact rec680 1 131 (by decide) (by decide)
      · right
        exact rec697 1 131 (by decide) (by decide)
      · right
        exact rec714 1 131 (by decide) (by decide)
      · right
        exact rec731 1 131 (by decide) (by decide)
      · right
        exact rec748 1 131 (by decide) (by decide)
      · right
        exact rec765 1 131 (by decide) (by decide)
      · right
        exact rec782 1 131 (by decide) (by decide)
      · right
        exact rec799 1 131 (by decide) (by decide)
      · right
        exact rec816 1 131 (by decide) (by decide)
      · right
        exact rec833 1 131 (by decide) (by decide)
      · right
        exact rec850 1 131 (by decide) (by decide)
      · right
        exact rec867 1 131 (by decide) (by decide)
      · right
        exact rec884 1 131 (by decide) (by decide)
      · right
        exact rec901 1 131 (by decide) (by decide)
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
        exact rec919 1 131 (by decide) (by decide)
      · right
        exact rec930 1 131 (by decide) (by decide)
      · right
        exact rec941 1 131 (by decide) (by decide)
      · right
        exact rec952 1 131 (by decide) (by decide)
      · right
        exact rec963 1 131 (by decide) (by decide)
      · right
        exact rec974 1 131 (by decide) (by decide)
      · right
        exact rec985 1 131 (by decide) (by decide)
      · right
        exact rec996 1 131 (by decide) (by decide)
      · right
        exact rec1007 1 131 (by decide) (by decide)
      · right
        exact rec1018 1 131 (by decide) (by decide)
      · right
        exact rec1029 1 131 (by decide) (by decide)
      · right
        exact rec1040 1 131 (by decide) (by decide)
      · right
        exact rec1051 1 131 (by decide) (by decide)
      · right
        exact rec1062 1 131 (by decide) (by decide)
      · right
        exact rec1073 1 131 (by decide) (by decide)
      · right
        exact rec1084 1 131 (by decide) (by decide)
      · right
        exact rec1095 1 131 (by decide) (by decide)
      · right
        exact rec1106 1 131 (by decide) (by decide)
      · right
        exact rec1117 1 131 (by decide) (by decide)
      · right
        exact rec1128 1 131 (by decide) (by decide)
      · right
        exact rec1139 1 131 (by decide) (by decide)
      · right
        exact rec1150 1 131 (by decide) (by decide)
      · right
        exact rec1161 1 131 (by decide) (by decide)
      · right
        exact rec1172 1 131 (by decide) (by decide)
      · right
        exact rec1183 1 131 (by decide) (by decide)
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
        exact rec1194 1 131 (by decide) (by decide)
      · right
        exact rec1201 1 131 (by decide) (by decide)
      · right
        exact rec1208 1 131 (by decide) (by decide)
      · right
        exact rec1215 1 131 (by decide) (by decide)
      · right
        exact rec1222 1 131 (by decide) (by decide)
      · right
        exact rec1229 1 131 (by decide) (by decide)
      · right
        exact rec1236 1 131 (by decide) (by decide)
      · right
        exact rec1243 1 131 (by decide) (by decide)
      · right
        exact rec1250 1 131 (by decide) (by decide)
      · right
        exact rec1257 1 131 (by decide) (by decide)
      · right
        exact rec1264 1 131 (by decide) (by decide)
      · right
        exact rec1271 1 131 (by decide) (by decide)
      · right
        exact rec1278 1 131 (by decide) (by decide)
      · right
        exact rec1285 1 131 (by decide) (by decide)
      · right
        exact rec1292 1 131 (by decide) (by decide)
      · right
        exact rec1299 1 131 (by decide) (by decide)
      · right
        exact rec1306 1 131 (by decide) (by decide)
      · right
        exact rec1313 1 131 (by decide) (by decide)
      · right
        exact rec1320 1 131 (by decide) (by decide)
      · right
        exact rec1327 1 131 (by decide) (by decide)
      · right
        exact rec1334 1 131 (by decide) (by decide)
      · right
        exact rec1341 1 131 (by decide) (by decide)
      · right
        exact rec1348 1 131 (by decide) (by decide)
      · right
        exact rec1355 1 131 (by decide) (by decide)
      · right
        exact rec1362 1 131 (by decide) (by decide)
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
        exact rec1371 1 131 (by decide) (by decide)
      · right
        exact rec1391 1 131 (by decide) (by decide)
      · right
        exact rec1415 1 131 (by decide) (by decide)
      · right
        exact rec1439 1 131 (by decide) (by decide)
      · right
        exact rec1463 1 131 (by decide) (by decide)
      · right
        exact rec1488 1 131 (by decide) (by decide)
      · right
        exact rec1508 1 131 (by decide) (by decide)
      · right
        exact rec1532 1 131 (by decide) (by decide)
      · right
        exact rec1556 1 131 (by decide) (by decide)
      · right
        exact rec1580 1 131 (by decide) (by decide)
      · right
        exact rec1605 1 131 (by decide) (by decide)
      · right
        exact rec1625 1 131 (by decide) (by decide)
      · right
        exact rec1649 1 131 (by decide) (by decide)
      · right
        exact rec1673 1 131 (by decide) (by decide)
      · right
        exact rec1697 1 131 (by decide) (by decide)
      · right
        exact rec1722 1 131 (by decide) (by decide)
      · right
        exact rec1742 1 131 (by decide) (by decide)
      · right
        exact rec1766 1 131 (by decide) (by decide)
      · right
        exact rec1790 1 131 (by decide) (by decide)
      · right
        exact rec1814 1 131 (by decide) (by decide)
      · right
        exact rec1839 1 131 (by decide) (by decide)
      · right
        exact rec1859 1 131 (by decide) (by decide)
      · right
        exact rec1883 1 131 (by decide) (by decide)
      · right
        exact rec1907 1 131 (by decide) (by decide)
      · right
        exact rec1931 1 131 (by decide) (by decide)
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
        exact rec1957 1 131 (by decide) (by decide)
      · right
        exact rec1973 1 131 (by decide) (by decide)
      · right
        exact rec1989 1 131 (by decide) (by decide)
      · right
        exact rec2005 1 131 (by decide) (by decide)
      · right
        exact rec2021 1 131 (by decide) (by decide)
      · right
        exact rec2037 1 131 (by decide) (by decide)
      · right
        exact rec2053 1 131 (by decide) (by decide)
      · right
        exact rec2069 1 131 (by decide) (by decide)
      · right
        exact rec2085 1 131 (by decide) (by decide)
      · right
        exact rec2101 1 131 (by decide) (by decide)
      · right
        exact rec2117 1 131 (by decide) (by decide)
      · right
        exact rec2133 1 131 (by decide) (by decide)
      · right
        exact rec2149 1 131 (by decide) (by decide)
      · right
        exact rec2165 1 131 (by decide) (by decide)
      · right
        exact rec2181 1 131 (by decide) (by decide)
      · right
        exact rec2197 1 131 (by decide) (by decide)
      · right
        exact rec2213 1 131 (by decide) (by decide)
      · right
        exact rec2229 1 131 (by decide) (by decide)
      · right
        exact rec2245 1 131 (by decide) (by decide)
      · right
        exact rec2261 1 131 (by decide) (by decide)
      · right
        exact rec2277 1 131 (by decide) (by decide)
      · right
        exact rec2293 1 131 (by decide) (by decide)
      · right
        exact rec2309 1 131 (by decide) (by decide)
      · right
        exact rec2325 1 131 (by decide) (by decide)
      · right
        exact rec2341 1 131 (by decide) (by decide)
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
        exact rec2359 1 131 (by decide) (by decide)
      · right
        exact rec2371 1 131 (by decide) (by decide)
      · right
        exact rec2392 1 131 (by decide) (by decide)
      · right
        exact rec2406 1 131 (by decide) (by decide)
      · right
        exact rec2430 1 131 (by decide) (by decide)
      · right
        exact rec2454 1 131 (by decide) (by decide)
      · right
        exact rec2478 1 131 (by decide) (by decide)
      · right
        exact rec2502 1 131 (by decide) (by decide)
      · right
        exact rec2526 1 131 (by decide) (by decide)
      · right
        exact rec2550 1 131 (by decide) (by decide)
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
        exact rec2574 1 131 (by decide) (by decide)
      · right
        exact rec2585 1 131 (by decide) (by decide)
      · right
        exact rec2597 1 131 (by decide) (by decide)
      · right
        exact rec2612 1 131 (by decide) (by decide)
      · right
        exact rec2622 1 131 (by decide) (by decide)
      · right
        exact rec2636 1 131 (by decide) (by decide)
      · right
        exact rec2648 1 131 (by decide) (by decide)
      · right
        exact rec2659 1 131 (by decide) (by decide)
      · right
        exact rec2667 1 131 (by decide) (by decide)
      · right
        exact rec2677 1 131 (by decide) (by decide)
      · right
        exact rec2687 1 131 (by decide) (by decide)
      · right
        exact rec2698 1 131 (by decide) (by decide)
      · right
        exact rec2708 1 131 (by decide) (by decide)
      · right
        exact rec2718 1 131 (by decide) (by decide)
      · right
        exact rec2732 1 131 (by decide) (by decide)
      · right
        exact rec2743 1 131 (by decide) (by decide)
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
        exact rec2753 1 131 (by decide) (by decide)
      · right
        exact rec2758 1 131 (by decide) (by decide)
      · right
        exact rec2765 1 131 (by decide) (by decide)
      · right
        exact rec2782 1 131 (by decide) (by decide)
      · right
        exact rec2790 1 131 (by decide) (by decide)
      · right
        exact rec2795 1 131 (by decide) (by decide)
      · right
        exact rec2802 1 131 (by decide) (by decide)
      · right
        exact rec2819 1 131 (by decide) (by decide)
      · right
        exact rec2827 1 131 (by decide) (by decide)
      · right
        exact rec2832 1 131 (by decide) (by decide)
      · right
        exact rec2839 1 131 (by decide) (by decide)
      · right
        exact rec2856 1 131 (by decide) (by decide)
      · right
        exact rec2864 1 131 (by decide) (by decide)
      · right
        exact rec2869 1 131 (by decide) (by decide)
      · right
        exact rec2876 1 131 (by decide) (by decide)
      · right
        exact rec2893 1 131 (by decide) (by decide)
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
        exact rec2900 1 131 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2911 1 131 (by decide) (by decide)
      · right
        exact rec2925 1 131 (by decide) (by decide)
      · right
        exact rec2938 1 131 (by decide) (by decide)
      · left
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
        exact rec2950 1 131 (by decide) (by decide)
      · right
        exact rec2962 1 131 (by decide) (by decide)
      · right
        exact rec2972 1 131 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2982 1 131 (by decide) (by decide)
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
    exact rec361 1 132 (by decide) (by decide)
  · left
    exact rec361 1 133 (by decide) (by decide)
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
        exact rec497 1 134 (by decide) (by decide)
      · right
        exact rec514 1 134 (by decide) (by decide)
      · right
        exact rec531 1 134 (by decide) (by decide)
      · right
        exact rec548 1 134 (by decide) (by decide)
      · right
        exact rec565 1 134 (by decide) (by decide)
      · right
        exact rec582 1 134 (by decide) (by decide)
      · right
        exact rec599 1 134 (by decide) (by decide)
      · right
        exact rec616 1 134 (by decide) (by decide)
      · right
        exact rec633 1 134 (by decide) (by decide)
      · right
        exact rec650 1 134 (by decide) (by decide)
      · right
        exact rec667 1 134 (by decide) (by decide)
      · right
        exact rec684 1 134 (by decide) (by decide)
      · right
        exact rec701 1 134 (by decide) (by decide)
      · right
        exact rec718 1 134 (by decide) (by decide)
      · right
        exact rec735 1 134 (by decide) (by decide)
      · right
        exact rec752 1 134 (by decide) (by decide)
      · right
        exact rec769 1 134 (by decide) (by decide)
      · right
        exact rec786 1 134 (by decide) (by decide)
      · right
        exact rec803 1 134 (by decide) (by decide)
      · right
        exact rec820 1 134 (by decide) (by decide)
      · right
        exact rec837 1 134 (by decide) (by decide)
      · right
        exact rec854 1 134 (by decide) (by decide)
      · right
        exact rec871 1 134 (by decide) (by decide)
      · right
        exact rec888 1 134 (by decide) (by decide)
      · right
        exact rec905 1 134 (by decide) (by decide)
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
        exact rec922 1 134 (by decide) (by decide)
      · right
        exact rec933 1 134 (by decide) (by decide)
      · right
        exact rec944 1 134 (by decide) (by decide)
      · right
        exact rec955 1 134 (by decide) (by decide)
      · right
        exact rec966 1 134 (by decide) (by decide)
      · right
        exact rec977 1 134 (by decide) (by decide)
      · right
        exact rec988 1 134 (by decide) (by decide)
      · right
        exact rec999 1 134 (by decide) (by decide)
      · right
        exact rec1010 1 134 (by decide) (by decide)
      · right
        exact rec1021 1 134 (by decide) (by decide)
      · right
        exact rec1032 1 134 (by decide) (by decide)
      · right
        exact rec1043 1 134 (by decide) (by decide)
      · right
        exact rec1054 1 134 (by decide) (by decide)
      · right
        exact rec1065 1 134 (by decide) (by decide)
      · right
        exact rec1076 1 134 (by decide) (by decide)
      · right
        exact rec1087 1 134 (by decide) (by decide)
      · right
        exact rec1098 1 134 (by decide) (by decide)
      · right
        exact rec1109 1 134 (by decide) (by decide)
      · right
        exact rec1120 1 134 (by decide) (by decide)
      · right
        exact rec1131 1 134 (by decide) (by decide)
      · right
        exact rec1142 1 134 (by decide) (by decide)
      · right
        exact rec1153 1 134 (by decide) (by decide)
      · right
        exact rec1164 1 134 (by decide) (by decide)
      · right
        exact rec1175 1 134 (by decide) (by decide)
      · right
        exact rec1186 1 134 (by decide) (by decide)
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
        exact rec1196 1 134 (by decide) (by decide)
      · right
        exact rec1203 1 134 (by decide) (by decide)
      · right
        exact rec1210 1 134 (by decide) (by decide)
      · right
        exact rec1217 1 134 (by decide) (by decide)
      · right
        exact rec1224 1 134 (by decide) (by decide)
      · right
        exact rec1231 1 134 (by decide) (by decide)
      · right
        exact rec1238 1 134 (by decide) (by decide)
      · right
        exact rec1245 1 134 (by decide) (by decide)
      · right
        exact rec1252 1 134 (by decide) (by decide)
      · right
        exact rec1259 1 134 (by decide) (by decide)
      · right
        exact rec1266 1 134 (by decide) (by decide)
      · right
        exact rec1273 1 134 (by decide) (by decide)
      · right
        exact rec1280 1 134 (by decide) (by decide)
      · right
        exact rec1287 1 134 (by decide) (by decide)
      · right
        exact rec1294 1 134 (by decide) (by decide)
      · right
        exact rec1301 1 134 (by decide) (by decide)
      · right
        exact rec1308 1 134 (by decide) (by decide)
      · right
        exact rec1315 1 134 (by decide) (by decide)
      · right
        exact rec1322 1 134 (by decide) (by decide)
      · right
        exact rec1329 1 134 (by decide) (by decide)
      · right
        exact rec1336 1 134 (by decide) (by decide)
      · right
        exact rec1343 1 134 (by decide) (by decide)
      · right
        exact rec1350 1 134 (by decide) (by decide)
      · right
        exact rec1357 1 134 (by decide) (by decide)
      · right
        exact rec1364 1 134 (by decide) (by decide)
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
        exact rec1374 1 134 (by decide) (by decide)
      · right
        exact rec1395 1 134 (by decide) (by decide)
      · right
        exact rec1419 1 134 (by decide) (by decide)
      · right
        exact rec1443 1 134 (by decide) (by decide)
      · right
        exact rec1467 1 134 (by decide) (by decide)
      · right
        exact rec1491 1 134 (by decide) (by decide)
      · right
        exact rec1512 1 134 (by decide) (by decide)
      · right
        exact rec1536 1 134 (by decide) (by decide)
      · right
        exact rec1560 1 134 (by decide) (by decide)
      · right
        exact rec1584 1 134 (by decide) (by decide)
      · right
        exact rec1608 1 134 (by decide) (by decide)
      · right
        exact rec1629 1 134 (by decide) (by decide)
      · right
        exact rec1653 1 134 (by decide) (by decide)
      · right
        exact rec1677 1 134 (by decide) (by decide)
      · right
        exact rec1701 1 134 (by decide) (by decide)
      · right
        exact rec1725 1 134 (by decide) (by decide)
      · right
        exact rec1746 1 134 (by decide) (by decide)
      · right
        exact rec1770 1 134 (by decide) (by decide)
      · right
        exact rec1794 1 134 (by decide) (by decide)
      · right
        exact rec1818 1 134 (by decide) (by decide)
      · right
        exact rec1842 1 134 (by decide) (by decide)
      · right
        exact rec1863 1 134 (by decide) (by decide)
      · right
        exact rec1887 1 134 (by decide) (by decide)
      · right
        exact rec1911 1 134 (by decide) (by decide)
      · right
        exact rec1935 1 134 (by decide) (by decide)
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
        exact rec1960 1 134 (by decide) (by decide)
      · right
        exact rec1976 1 134 (by decide) (by decide)
      · right
        exact rec1992 1 134 (by decide) (by decide)
      · right
        exact rec2008 1 134 (by decide) (by decide)
      · right
        exact rec2024 1 134 (by decide) (by decide)
      · right
        exact rec2040 1 134 (by decide) (by decide)
      · right
        exact rec2056 1 134 (by decide) (by decide)
      · right
        exact rec2072 1 134 (by decide) (by decide)
      · right
        exact rec2088 1 134 (by decide) (by decide)
      · right
        exact rec2104 1 134 (by decide) (by decide)
      · right
        exact rec2120 1 134 (by decide) (by decide)
      · right
        exact rec2136 1 134 (by decide) (by decide)
      · right
        exact rec2152 1 134 (by decide) (by decide)
      · right
        exact rec2168 1 134 (by decide) (by decide)
      · right
        exact rec2184 1 134 (by decide) (by decide)
      · right
        exact rec2200 1 134 (by decide) (by decide)
      · right
        exact rec2216 1 134 (by decide) (by decide)
      · right
        exact rec2232 1 134 (by decide) (by decide)
      · right
        exact rec2248 1 134 (by decide) (by decide)
      · right
        exact rec2264 1 134 (by decide) (by decide)
      · right
        exact rec2280 1 134 (by decide) (by decide)
      · right
        exact rec2296 1 134 (by decide) (by decide)
      · right
        exact rec2312 1 134 (by decide) (by decide)
      · right
        exact rec2328 1 134 (by decide) (by decide)
      · right
        exact rec2344 1 134 (by decide) (by decide)
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
        exact rec2353 1 134 (by decide) (by decide)
      · right
        exact rec2369 1 134 (by decide) (by decide)
      · right
        exact rec2390 1 134 (by decide) (by decide)
      · right
        exact rec2412 1 134 (by decide) (by decide)
      · right
        exact rec2436 1 134 (by decide) (by decide)
      · right
        exact rec2460 1 134 (by decide) (by decide)
      · right
        exact rec2484 1 134 (by decide) (by decide)
      · right
        exact rec2508 1 134 (by decide) (by decide)
      · right
        exact rec2532 1 134 (by decide) (by decide)
      · right
        exact rec2556 1 134 (by decide) (by decide)
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
        exact rec2575 1 134 (by decide) (by decide)
      · right
        exact rec2584 1 134 (by decide) (by decide)
      · right
        exact rec2597 1 134 (by decide) (by decide)
      · right
        exact rec2610 1 134 (by decide) (by decide)
      · right
        exact rec2623 1 134 (by decide) (by decide)
      · right
        exact rec2635 1 134 (by decide) (by decide)
      · right
        exact rec2646 1 134 (by decide) (by decide)
      · right
        exact rec2657 1 134 (by decide) (by decide)
      · right
        exact rec2671 1 134 (by decide) (by decide)
      · right
        exact rec2681 1 134 (by decide) (by decide)
      · right
        exact rec2686 1 134 (by decide) (by decide)
      · right
        exact rec2701 1 134 (by decide) (by decide)
      · right
        exact rec2710 1 134 (by decide) (by decide)
      · right
        exact rec2722 1 134 (by decide) (by decide)
      · right
        exact rec2735 1 134 (by decide) (by decide)
      · right
        exact rec2746 1 134 (by decide) (by decide)
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
        exact rec2754 1 134 (by decide) (by decide)
      · right
        exact rec2759 1 134 (by decide) (by decide)
      · right
        exact rec2769 1 134 (by decide) (by decide)
      · right
        exact rec2783 1 134 (by decide) (by decide)
      · right
        exact rec2791 1 134 (by decide) (by decide)
      · right
        exact rec2796 1 134 (by decide) (by decide)
      · right
        exact rec2806 1 134 (by decide) (by decide)
      · right
        exact rec2820 1 134 (by decide) (by decide)
      · right
        exact rec2828 1 134 (by decide) (by decide)
      · right
        exact rec2833 1 134 (by decide) (by decide)
      · right
        exact rec2843 1 134 (by decide) (by decide)
      · right
        exact rec2857 1 134 (by decide) (by decide)
      · right
        exact rec2865 1 134 (by decide) (by decide)
      · right
        exact rec2870 1 134 (by decide) (by decide)
      · right
        exact rec2880 1 134 (by decide) (by decide)
      · right
        exact rec2894 1 134 (by decide) (by decide)
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
        exact rec2903 1 134 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2913 1 134 (by decide) (by decide)
      · right
        exact rec2923 1 134 (by decide) (by decide)
      · right
        exact rec2936 1 134 (by decide) (by decide)
      · left
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
        exact rec2953 1 134 (by decide) (by decide)
      · right
        exact rec2960 1 134 (by decide) (by decide)
      · right
        exact rec2970 1 134 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2981 1 134 (by decide) (by decide)
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
        exact rec498 1 135 (by decide) (by decide)
      · right
        exact rec515 1 135 (by decide) (by decide)
      · right
        exact rec532 1 135 (by decide) (by decide)
      · right
        exact rec549 1 135 (by decide) (by decide)
      · right
        exact rec566 1 135 (by decide) (by decide)
      · right
        exact rec583 1 135 (by decide) (by decide)
      · right
        exact rec600 1 135 (by decide) (by decide)
      · right
        exact rec617 1 135 (by decide) (by decide)
      · right
        exact rec634 1 135 (by decide) (by decide)
      · right
        exact rec651 1 135 (by decide) (by decide)
      · right
        exact rec668 1 135 (by decide) (by decide)
      · right
        exact rec685 1 135 (by decide) (by decide)
      · right
        exact rec702 1 135 (by decide) (by decide)
      · right
        exact rec719 1 135 (by decide) (by decide)
      · right
        exact rec736 1 135 (by decide) (by decide)
      · right
        exact rec753 1 135 (by decide) (by decide)
      · right
        exact rec770 1 135 (by decide) (by decide)
      · right
        exact rec787 1 135 (by decide) (by decide)
      · right
        exact rec804 1 135 (by decide) (by decide)
      · right
        exact rec821 1 135 (by decide) (by decide)
      · right
        exact rec838 1 135 (by decide) (by decide)
      · right
        exact rec855 1 135 (by decide) (by decide)
      · right
        exact rec872 1 135 (by decide) (by decide)
      · right
        exact rec889 1 135 (by decide) (by decide)
      · right
        exact rec906 1 135 (by decide) (by decide)
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
        exact rec923 1 135 (by decide) (by decide)
      · right
        exact rec934 1 135 (by decide) (by decide)
      · right
        exact rec945 1 135 (by decide) (by decide)
      · right
        exact rec956 1 135 (by decide) (by decide)
      · right
        exact rec967 1 135 (by decide) (by decide)
      · right
        exact rec978 1 135 (by decide) (by decide)
      · right
        exact rec989 1 135 (by decide) (by decide)
      · right
        exact rec1000 1 135 (by decide) (by decide)
      · right
        exact rec1011 1 135 (by decide) (by decide)
      · right
        exact rec1022 1 135 (by decide) (by decide)
      · right
        exact rec1033 1 135 (by decide) (by decide)
      · right
        exact rec1044 1 135 (by decide) (by decide)
      · right
        exact rec1055 1 135 (by decide) (by decide)
      · right
        exact rec1066 1 135 (by decide) (by decide)
      · right
        exact rec1077 1 135 (by decide) (by decide)
      · right
        exact rec1088 1 135 (by decide) (by decide)
      · right
        exact rec1099 1 135 (by decide) (by decide)
      · right
        exact rec1110 1 135 (by decide) (by decide)
      · right
        exact rec1121 1 135 (by decide) (by decide)
      · right
        exact rec1132 1 135 (by decide) (by decide)
      · right
        exact rec1143 1 135 (by decide) (by decide)
      · right
        exact rec1154 1 135 (by decide) (by decide)
      · right
        exact rec1165 1 135 (by decide) (by decide)
      · right
        exact rec1176 1 135 (by decide) (by decide)
      · right
        exact rec1187 1 135 (by decide) (by decide)
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
        exact rec1197 1 135 (by decide) (by decide)
      · right
        exact rec1204 1 135 (by decide) (by decide)
      · right
        exact rec1211 1 135 (by decide) (by decide)
      · right
        exact rec1218 1 135 (by decide) (by decide)
      · right
        exact rec1225 1 135 (by decide) (by decide)
      · right
        exact rec1232 1 135 (by decide) (by decide)
      · right
        exact rec1239 1 135 (by decide) (by decide)
      · right
        exact rec1246 1 135 (by decide) (by decide)
      · right
        exact rec1253 1 135 (by decide) (by decide)
      · right
        exact rec1260 1 135 (by decide) (by decide)
      · right
        exact rec1267 1 135 (by decide) (by decide)
      · right
        exact rec1274 1 135 (by decide) (by decide)
      · right
        exact rec1281 1 135 (by decide) (by decide)
      · right
        exact rec1288 1 135 (by decide) (by decide)
      · right
        exact rec1295 1 135 (by decide) (by decide)
      · right
        exact rec1302 1 135 (by decide) (by decide)
      · right
        exact rec1309 1 135 (by decide) (by decide)
      · right
        exact rec1316 1 135 (by decide) (by decide)
      · right
        exact rec1323 1 135 (by decide) (by decide)
      · right
        exact rec1330 1 135 (by decide) (by decide)
      · right
        exact rec1337 1 135 (by decide) (by decide)
      · right
        exact rec1344 1 135 (by decide) (by decide)
      · right
        exact rec1351 1 135 (by decide) (by decide)
      · right
        exact rec1358 1 135 (by decide) (by decide)
      · right
        exact rec1365 1 135 (by decide) (by decide)
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
        exact rec1375 1 135 (by decide) (by decide)
      · right
        exact rec1396 1 135 (by decide) (by decide)
      · right
        exact rec1420 1 135 (by decide) (by decide)
      · right
        exact rec1444 1 135 (by decide) (by decide)
      · right
        exact rec1468 1 135 (by decide) (by decide)
      · right
        exact rec1492 1 135 (by decide) (by decide)
      · right
        exact rec1513 1 135 (by decide) (by decide)
      · right
        exact rec1537 1 135 (by decide) (by decide)
      · right
        exact rec1561 1 135 (by decide) (by decide)
      · right
        exact rec1585 1 135 (by decide) (by decide)
      · right
        exact rec1609 1 135 (by decide) (by decide)
      · right
        exact rec1630 1 135 (by decide) (by decide)
      · right
        exact rec1654 1 135 (by decide) (by decide)
      · right
        exact rec1678 1 135 (by decide) (by decide)
      · right
        exact rec1702 1 135 (by decide) (by decide)
      · right
        exact rec1726 1 135 (by decide) (by decide)
      · right
        exact rec1747 1 135 (by decide) (by decide)
      · right
        exact rec1771 1 135 (by decide) (by decide)
      · right
        exact rec1795 1 135 (by decide) (by decide)
      · right
        exact rec1819 1 135 (by decide) (by decide)
      · right
        exact rec1843 1 135 (by decide) (by decide)
      · right
        exact rec1864 1 135 (by decide) (by decide)
      · right
        exact rec1888 1 135 (by decide) (by decide)
      · right
        exact rec1912 1 135 (by decide) (by decide)
      · right
        exact rec1936 1 135 (by decide) (by decide)
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
        exact rec1960 1 135 (by decide) (by decide)
      · right
        exact rec1976 1 135 (by decide) (by decide)
      · right
        exact rec1992 1 135 (by decide) (by decide)
      · right
        exact rec2008 1 135 (by decide) (by decide)
      · right
        exact rec2024 1 135 (by decide) (by decide)
      · right
        exact rec2040 1 135 (by decide) (by decide)
      · right
        exact rec2056 1 135 (by decide) (by decide)
      · right
        exact rec2072 1 135 (by decide) (by decide)
      · right
        exact rec2088 1 135 (by decide) (by decide)
      · right
        exact rec2104 1 135 (by decide) (by decide)
      · right
        exact rec2120 1 135 (by decide) (by decide)
      · right
        exact rec2136 1 135 (by decide) (by decide)
      · right
        exact rec2152 1 135 (by decide) (by decide)
      · right
        exact rec2168 1 135 (by decide) (by decide)
      · right
        exact rec2184 1 135 (by decide) (by decide)
      · right
        exact rec2200 1 135 (by decide) (by decide)
      · right
        exact rec2216 1 135 (by decide) (by decide)
      · right
        exact rec2232 1 135 (by decide) (by decide)
      · right
        exact rec2248 1 135 (by decide) (by decide)
      · right
        exact rec2264 1 135 (by decide) (by decide)
      · right
        exact rec2280 1 135 (by decide) (by decide)
      · right
        exact rec2296 1 135 (by decide) (by decide)
      · right
        exact rec2312 1 135 (by decide) (by decide)
      · right
        exact rec2328 1 135 (by decide) (by decide)
      · right
        exact rec2344 1 135 (by decide) (by decide)
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
        exact rec2354 1 135 (by decide) (by decide)
      · right
        exact rec2369 1 135 (by decide) (by decide)
      · right
        exact rec2391 1 135 (by decide) (by decide)
      · right
        exact rec2404 1 135 (by decide) (by decide)
      · right
        exact rec2428 1 135 (by decide) (by decide)
      · right
        exact rec2452 1 135 (by decide) (by decide)
      · right
        exact rec2476 1 135 (by decide) (by decide)
      · right
        exact rec2500 1 135 (by decide) (by decide)
      · right
        exact rec2524 1 135 (by decide) (by decide)
      · right
        exact rec2548 1 135 (by decide) (by decide)
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
        exact rec2575 1 135 (by decide) (by decide)
      · right
        exact rec2584 1 135 (by decide) (by decide)
      · right
        exact rec2597 1 135 (by decide) (by decide)
      · right
        exact rec2613 1 135 (by decide) (by decide)
      · right
        exact rec2625 1 135 (by decide) (by decide)
      · right
        exact rec2635 1 135 (by decide) (by decide)
      · right
        exact rec2649 1 135 (by decide) (by decide)
      · right
        exact rec2660 1 135 (by decide) (by decide)
      · right
        exact rec2672 1 135 (by decide) (by decide)
      · right
        exact rec2682 1 135 (by decide) (by decide)
      · right
        exact rec2686 1 135 (by decide) (by decide)
      · right
        exact rec2702 1 135 (by decide) (by decide)
      · right
        exact rec2711 1 135 (by decide) (by decide)
      · right
        exact rec2722 1 135 (by decide) (by decide)
      · right
        exact rec2735 1 135 (by decide) (by decide)
      · right
        exact rec2746 1 135 (by decide) (by decide)
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
        exact rec2754 1 135 (by decide) (by decide)
      · right
        exact rec2759 1 135 (by decide) (by decide)
      · right
        exact rec2768 1 135 (by decide) (by decide)
      · right
        exact rec2784 1 135 (by decide) (by decide)
      · right
        exact rec2791 1 135 (by decide) (by decide)
      · right
        exact rec2796 1 135 (by decide) (by decide)
      · right
        exact rec2804 1 135 (by decide) (by decide)
      · right
        exact rec2821 1 135 (by decide) (by decide)
      · right
        exact rec2828 1 135 (by decide) (by decide)
      · right
        exact rec2833 1 135 (by decide) (by decide)
      · right
        exact rec2841 1 135 (by decide) (by decide)
      · right
        exact rec2858 1 135 (by decide) (by decide)
      · right
        exact rec2865 1 135 (by decide) (by decide)
      · right
        exact rec2870 1 135 (by decide) (by decide)
      · right
        exact rec2878 1 135 (by decide) (by decide)
      · right
        exact rec2895 1 135 (by decide) (by decide)
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
        exact rec2904 1 135 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2914 1 135 (by decide) (by decide)
      · right
        exact rec2926 1 135 (by decide) (by decide)
      · right
        exact rec2937 1 135 (by decide) (by decide)
      · left
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
        exact rec2953 1 135 (by decide) (by decide)
      · right
        exact rec2963 1 135 (by decide) (by decide)
      · right
        exact rec2970 1 135 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2981 1 135 (by decide) (by decide)
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
    exact rec388 1 136 (by decide) (by decide)
  · left
    exact rec388 1 137 (by decide) (by decide)
  · left
    exact rec362 1 138 (by decide) (by decide)
  · left
    exact rec362 1 139 (by decide) (by decide)
  · left
    exact rec388 1 140 (by decide) (by decide)
  · left
    exact rec388 1 141 (by decide) (by decide)
  · left
    exact rec362 1 142 (by decide) (by decide)
  · left
    exact rec362 1 143 (by decide) (by decide)
end Section14Coverage_1_1_p128_144

end WorkReverseInterface_Freiman_workReverse20260919_s0001_coverage0001_parents_0128_0144


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_coverage0001_parents_0144_0160
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_1_1_p144_160
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec494 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[494]? = some (⟨18,(0),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec499 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,13],[146],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[499]? = some (⟨18,(0),[1,13],[146],73⟩) from rfl))
private theorem rec500 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,13],[151],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[500]? = some (⟨18,(0),[1,13],[151],125⟩) from rfl))
private theorem rec501 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,13],[147],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[501]? = some (⟨18,(0),[1,13],[147],160⟩) from rfl))
private theorem rec511 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[511]? = some (⟨18,(1),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec516 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,13],[146],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[516]? = some (⟨18,(1),[1,13],[146],73⟩) from rfl))
private theorem rec517 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,13],[151],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[517]? = some (⟨18,(1),[1,13],[151],125⟩) from rfl))
private theorem rec518 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,13],[147],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[518]? = some (⟨18,(1),[1,13],[147],160⟩) from rfl))
private theorem rec528 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[528]? = some (⟨18,(2),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec533 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,13],[146],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[533]? = some (⟨18,(2),[1,13],[146],73⟩) from rfl))
private theorem rec534 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,13],[151],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[534]? = some (⟨18,(2),[1,13],[151],125⟩) from rfl))
private theorem rec535 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,13],[147],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[535]? = some (⟨18,(2),[1,13],[147],160⟩) from rfl))
private theorem rec545 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[545]? = some (⟨18,(3),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec550 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,13],[146],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[550]? = some (⟨18,(3),[1,13],[146],73⟩) from rfl))
private theorem rec551 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,13],[151],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[551]? = some (⟨18,(3),[1,13],[151],125⟩) from rfl))
private theorem rec552 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,13],[147],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[552]? = some (⟨18,(3),[1,13],[147],160⟩) from rfl))
private theorem rec562 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[562]? = some (⟨18,(4),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec567 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,13],[146],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[567]? = some (⟨18,(4),[1,13],[146],73⟩) from rfl))
private theorem rec568 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,13],[151],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[568]? = some (⟨18,(4),[1,13],[151],125⟩) from rfl))
private theorem rec569 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,13],[147],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[569]? = some (⟨18,(4),[1,13],[147],160⟩) from rfl))
private theorem rec579 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[579]? = some (⟨18,(5),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec584 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,13],[146],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[584]? = some (⟨18,(5),[1,13],[146],74⟩) from rfl))
private theorem rec585 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,13],[151],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[585]? = some (⟨18,(5),[1,13],[151],126⟩) from rfl))
private theorem rec586 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,13],[147],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[586]? = some (⟨18,(5),[1,13],[147],161⟩) from rfl))
private theorem rec596 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[596]? = some (⟨18,(6),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec601 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,13],[146],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[601]? = some (⟨18,(6),[1,13],[146],74⟩) from rfl))
private theorem rec602 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,13],[151],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[602]? = some (⟨18,(6),[1,13],[151],126⟩) from rfl))
private theorem rec603 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,13],[147],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[603]? = some (⟨18,(6),[1,13],[147],161⟩) from rfl))
private theorem rec613 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[613]? = some (⟨18,(7),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec618 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,13],[146],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[618]? = some (⟨18,(7),[1,13],[146],74⟩) from rfl))
private theorem rec619 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,13],[151],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[619]? = some (⟨18,(7),[1,13],[151],126⟩) from rfl))
private theorem rec620 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,13],[147],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[620]? = some (⟨18,(7),[1,13],[147],161⟩) from rfl))
private theorem rec630 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[630]? = some (⟨18,(8),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec635 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,13],[146],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[635]? = some (⟨18,(8),[1,13],[146],74⟩) from rfl))
private theorem rec636 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,13],[151],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[636]? = some (⟨18,(8),[1,13],[151],126⟩) from rfl))
private theorem rec637 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,13],[147],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[637]? = some (⟨18,(8),[1,13],[147],161⟩) from rfl))
private theorem rec647 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[647]? = some (⟨18,(9),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec652 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,13],[146],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[652]? = some (⟨18,(9),[1,13],[146],74⟩) from rfl))
private theorem rec653 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,13],[151],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[653]? = some (⟨18,(9),[1,13],[151],126⟩) from rfl))
private theorem rec654 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,13],[147],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[654]? = some (⟨18,(9),[1,13],[147],161⟩) from rfl))
private theorem rec664 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,2,5,6,13,14],[150],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[664]? = some (⟨18,(10),[1,2,5,6,13,14],[150],127⟩) from rfl))
private theorem rec669 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,13],[146],75⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[669]? = some (⟨18,(10),[1,13],[146],75⟩) from rfl))
private theorem rec670 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,13],[151],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[670]? = some (⟨18,(10),[1,13],[151],127⟩) from rfl))
private theorem rec671 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,13],[147],162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[671]? = some (⟨18,(10),[1,13],[147],162⟩) from rfl))
private theorem rec681 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,2,5,6,13,14],[150],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[681]? = some (⟨18,(11),[1,2,5,6,13,14],[150],128⟩) from rfl))
private theorem rec686 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,13],[146],76⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[686]? = some (⟨18,(11),[1,13],[146],76⟩) from rfl))
private theorem rec687 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,13],[151],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[687]? = some (⟨18,(11),[1,13],[151],128⟩) from rfl))
private theorem rec688 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,13],[147],163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[688]? = some (⟨18,(11),[1,13],[147],163⟩) from rfl))
private theorem rec698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,2,5,6,13,14],[150],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[698]? = some (⟨18,(12),[1,2,5,6,13,14],[150],129⟩) from rfl))
private theorem rec703 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,13],[146],77⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[703]? = some (⟨18,(12),[1,13],[146],77⟩) from rfl))
private theorem rec704 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,13],[151],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[704]? = some (⟨18,(12),[1,13],[151],129⟩) from rfl))
private theorem rec705 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,13],[147],164⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[705]? = some (⟨18,(12),[1,13],[147],164⟩) from rfl))
private theorem rec715 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,2,5,6,13,14],[150],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[715]? = some (⟨18,(13),[1,2,5,6,13,14],[150],128⟩) from rfl))
private theorem rec720 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,13],[146],76⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[720]? = some (⟨18,(13),[1,13],[146],76⟩) from rfl))
private theorem rec721 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,13],[151],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[721]? = some (⟨18,(13),[1,13],[151],128⟩) from rfl))
private theorem rec722 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,13],[147],163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[722]? = some (⟨18,(13),[1,13],[147],163⟩) from rfl))
private theorem rec732 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,2,5,6,13,14],[150],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[732]? = some (⟨18,(14),[1,2,5,6,13,14],[150],130⟩) from rfl))
private theorem rec737 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,13],[146],78⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[737]? = some (⟨18,(14),[1,13],[146],78⟩) from rfl))
private theorem rec738 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,13],[151],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[738]? = some (⟨18,(14),[1,13],[151],130⟩) from rfl))
private theorem rec739 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,13],[147],165⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[739]? = some (⟨18,(14),[1,13],[147],165⟩) from rfl))
private theorem rec749 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,2,5,6,13,14],[150],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[749]? = some (⟨18,(15),[1,2,5,6,13,14],[150],127⟩) from rfl))
private theorem rec754 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,13],[146],75⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[754]? = some (⟨18,(15),[1,13],[146],75⟩) from rfl))
private theorem rec755 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,13],[151],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[755]? = some (⟨18,(15),[1,13],[151],127⟩) from rfl))
private theorem rec756 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,13],[147],162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[756]? = some (⟨18,(15),[1,13],[147],162⟩) from rfl))
private theorem rec766 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,2,5,6,13,14],[150],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[766]? = some (⟨18,(16),[1,2,5,6,13,14],[150],131⟩) from rfl))
private theorem rec771 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,13],[146],79⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[771]? = some (⟨18,(16),[1,13],[146],79⟩) from rfl))
private theorem rec772 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,13],[151],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[772]? = some (⟨18,(16),[1,13],[151],131⟩) from rfl))
private theorem rec773 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,13],[147],166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[773]? = some (⟨18,(16),[1,13],[147],166⟩) from rfl))
private theorem rec783 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,2,5,6,13,14],[150],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[783]? = some (⟨18,(17),[1,2,5,6,13,14],[150],131⟩) from rfl))
private theorem rec788 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,13],[146],79⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[788]? = some (⟨18,(17),[1,13],[146],79⟩) from rfl))
private theorem rec789 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,13],[151],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[789]? = some (⟨18,(17),[1,13],[151],131⟩) from rfl))
private theorem rec790 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,13],[147],166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[790]? = some (⟨18,(17),[1,13],[147],166⟩) from rfl))
private theorem rec800 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,2,5,6,13,14],[150],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[800]? = some (⟨18,(18),[1,2,5,6,13,14],[150],131⟩) from rfl))
private theorem rec805 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,13],[146],79⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[805]? = some (⟨18,(18),[1,13],[146],79⟩) from rfl))
private theorem rec806 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,13],[151],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[806]? = some (⟨18,(18),[1,13],[151],131⟩) from rfl))
private theorem rec807 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,13],[147],166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[807]? = some (⟨18,(18),[1,13],[147],166⟩) from rfl))
private theorem rec817 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,2,5,6,13,14],[150],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[817]? = some (⟨18,(19),[1,2,5,6,13,14],[150],131⟩) from rfl))
private theorem rec822 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,13],[146],79⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[822]? = some (⟨18,(19),[1,13],[146],79⟩) from rfl))
private theorem rec823 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,13],[151],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[823]? = some (⟨18,(19),[1,13],[151],131⟩) from rfl))
private theorem rec824 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,13],[147],166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[824]? = some (⟨18,(19),[1,13],[147],166⟩) from rfl))
private theorem rec834 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,2,5,6,13,14],[150],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[834]? = some (⟨18,(20),[1,2,5,6,13,14],[150],127⟩) from rfl))
private theorem rec839 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,13],[146],75⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[839]? = some (⟨18,(20),[1,13],[146],75⟩) from rfl))
private theorem rec840 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,13],[151],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[840]? = some (⟨18,(20),[1,13],[151],127⟩) from rfl))
private theorem rec841 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,13],[147],162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[841]? = some (⟨18,(20),[1,13],[147],162⟩) from rfl))
private theorem rec851 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,2,5,6,13,14],[150],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[851]? = some (⟨18,(21),[1,2,5,6,13,14],[150],128⟩) from rfl))
private theorem rec856 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,13],[146],76⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[856]? = some (⟨18,(21),[1,13],[146],76⟩) from rfl))
private theorem rec857 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,13],[151],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[857]? = some (⟨18,(21),[1,13],[151],128⟩) from rfl))
private theorem rec858 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,13],[147],163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[858]? = some (⟨18,(21),[1,13],[147],163⟩) from rfl))
private theorem rec868 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,2,5,6,13,14],[150],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[868]? = some (⟨18,(22),[1,2,5,6,13,14],[150],129⟩) from rfl))
private theorem rec873 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,13],[146],77⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[873]? = some (⟨18,(22),[1,13],[146],77⟩) from rfl))
private theorem rec874 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,13],[151],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[874]? = some (⟨18,(22),[1,13],[151],129⟩) from rfl))
private theorem rec875 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,13],[147],164⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[875]? = some (⟨18,(22),[1,13],[147],164⟩) from rfl))
private theorem rec885 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,2,5,6,13,14],[150],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[885]? = some (⟨18,(23),[1,2,5,6,13,14],[150],128⟩) from rfl))
private theorem rec890 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,13],[146],76⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[890]? = some (⟨18,(23),[1,13],[146],76⟩) from rfl))
private theorem rec891 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,13],[151],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[891]? = some (⟨18,(23),[1,13],[151],128⟩) from rfl))
private theorem rec892 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,13],[147],163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[892]? = some (⟨18,(23),[1,13],[147],163⟩) from rfl))
private theorem rec902 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,2,5,6,13,14],[150],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[902]? = some (⟨18,(24),[1,2,5,6,13,14],[150],130⟩) from rfl))
private theorem rec907 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,13],[146],78⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[907]? = some (⟨18,(24),[1,13],[146],78⟩) from rfl))
private theorem rec908 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,13],[151],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[908]? = some (⟨18,(24),[1,13],[151],130⟩) from rfl))
private theorem rec909 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,13],[147],165⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[909]? = some (⟨18,(24),[1,13],[147],165⟩) from rfl))
private theorem rec919 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[919]? = some (⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec920 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[920]? = some (⟨20,(0),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec924 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[924]? = some (⟨20,(0),[1,13],[151],3⟩) from rfl))
private theorem rec930 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[930]? = some (⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec931 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[931]? = some (⟨20,(1),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec935 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[935]? = some (⟨20,(1),[1,13],[151],3⟩) from rfl))
private theorem rec941 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[941]? = some (⟨20,(2),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec942 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[942]? = some (⟨20,(2),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec946 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[946]? = some (⟨20,(2),[1,13],[151],3⟩) from rfl))
private theorem rec952 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[952]? = some (⟨20,(3),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec953 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[953]? = some (⟨20,(3),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec957 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[957]? = some (⟨20,(3),[1,13],[151],3⟩) from rfl))
private theorem rec963 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[963]? = some (⟨20,(4),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec964 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[964]? = some (⟨20,(4),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec968 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[968]? = some (⟨20,(4),[1,13],[151],3⟩) from rfl))
private theorem rec974 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[974]? = some (⟨20,(5),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec975 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[975]? = some (⟨20,(5),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec979 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[979]? = some (⟨20,(5),[1,13],[151],3⟩) from rfl))
private theorem rec985 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[985]? = some (⟨20,(6),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec986 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[986]? = some (⟨20,(6),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec990 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[990]? = some (⟨20,(6),[1,13],[151],3⟩) from rfl))
private theorem rec996 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[996]? = some (⟨20,(7),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec997 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[997]? = some (⟨20,(7),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1001 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1001]? = some (⟨20,(7),[1,13],[151],3⟩) from rfl))
private theorem rec1007 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1007]? = some (⟨20,(8),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1008 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1008]? = some (⟨20,(8),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1012 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1012]? = some (⟨20,(8),[1,13],[151],3⟩) from rfl))
private theorem rec1018 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1018]? = some (⟨20,(9),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1019 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1019]? = some (⟨20,(9),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1023 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1023]? = some (⟨20,(9),[1,13],[151],3⟩) from rfl))
private theorem rec1029 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1029]? = some (⟨20,(10),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1030 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1030]? = some (⟨20,(10),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1034 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1034]? = some (⟨20,(10),[1,13],[151],3⟩) from rfl))
private theorem rec1040 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1040]? = some (⟨20,(11),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1041 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1041]? = some (⟨20,(11),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1045 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1045]? = some (⟨20,(11),[1,13],[151],3⟩) from rfl))
private theorem rec1051 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1051]? = some (⟨20,(12),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1052 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1052]? = some (⟨20,(12),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1056 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1056]? = some (⟨20,(12),[1,13],[151],3⟩) from rfl))
private theorem rec1062 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1062]? = some (⟨20,(13),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1063 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1063]? = some (⟨20,(13),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1067 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1067]? = some (⟨20,(13),[1,13],[151],3⟩) from rfl))
private theorem rec1073 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1073]? = some (⟨20,(14),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1074 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1074]? = some (⟨20,(14),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1078 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1078]? = some (⟨20,(14),[1,13],[151],3⟩) from rfl))
private theorem rec1084 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1084]? = some (⟨20,(15),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1085 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1085]? = some (⟨20,(15),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1089 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1089]? = some (⟨20,(15),[1,13],[151],3⟩) from rfl))
private theorem rec1095 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1095]? = some (⟨20,(16),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1096 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1096]? = some (⟨20,(16),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1100 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1100]? = some (⟨20,(16),[1,13],[151],3⟩) from rfl))
private theorem rec1106 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1106]? = some (⟨20,(17),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1107 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1107]? = some (⟨20,(17),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1111 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1111]? = some (⟨20,(17),[1,13],[151],3⟩) from rfl))
private theorem rec1117 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1117]? = some (⟨20,(18),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1118 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1118]? = some (⟨20,(18),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1122 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1122]? = some (⟨20,(18),[1,13],[151],3⟩) from rfl))
private theorem rec1128 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1128]? = some (⟨20,(19),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1129 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1129]? = some (⟨20,(19),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1133 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1133]? = some (⟨20,(19),[1,13],[151],3⟩) from rfl))
private theorem rec1139 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1139]? = some (⟨20,(20),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1140 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1140]? = some (⟨20,(20),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1144 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1144]? = some (⟨20,(20),[1,13],[151],3⟩) from rfl))
private theorem rec1150 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1150]? = some (⟨20,(21),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1151 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1151]? = some (⟨20,(21),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1155 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1155]? = some (⟨20,(21),[1,13],[151],3⟩) from rfl))
private theorem rec1161 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1161]? = some (⟨20,(22),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1162 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1162]? = some (⟨20,(22),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1166 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1166]? = some (⟨20,(22),[1,13],[151],3⟩) from rfl))
private theorem rec1172 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[3]? = some (⟨20,(23),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1173 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[4]? = some (⟨20,(23),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1177 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[8]? = some (⟨20,(23),[1,13],[151],3⟩) from rfl))
private theorem rec1183 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[14]? = some (⟨20,(24),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1184 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[15]? = some (⟨20,(24),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec1188 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[19]? = some (⟨20,(24),[1,13],[151],3⟩) from rfl))
private theorem rec1194 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[25]? = some (⟨23,(0),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1195 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[26]? = some (⟨23,(0),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1198 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[29]? = some (⟨23,(0),[1,13],[151],2⟩) from rfl))
private theorem rec1201 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[32]? = some (⟨23,(1),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1202 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[33]? = some (⟨23,(1),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1205 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[36]? = some (⟨23,(1),[1,13],[151],2⟩) from rfl))
private theorem rec1208 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[39]? = some (⟨23,(2),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1209 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[40]? = some (⟨23,(2),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1212 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[43]? = some (⟨23,(2),[1,13],[151],2⟩) from rfl))
private theorem rec1215 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[46]? = some (⟨23,(3),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1216 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[47]? = some (⟨23,(3),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1219 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[50]? = some (⟨23,(3),[1,13],[151],2⟩) from rfl))
private theorem rec1222 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[53]? = some (⟨23,(4),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1223 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[54]? = some (⟨23,(4),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1226 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[57]? = some (⟨23,(4),[1,13],[151],2⟩) from rfl))
private theorem rec1229 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[60]? = some (⟨23,(5),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1230 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[61]? = some (⟨23,(5),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1233 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[64]? = some (⟨23,(5),[1,13],[151],2⟩) from rfl))
private theorem rec1236 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[67]? = some (⟨23,(6),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1237 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[68]? = some (⟨23,(6),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1240 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[71]? = some (⟨23,(6),[1,13],[151],2⟩) from rfl))
private theorem rec1243 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[74]? = some (⟨23,(7),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1244 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[75]? = some (⟨23,(7),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1247 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[78]? = some (⟨23,(7),[1,13],[151],2⟩) from rfl))
private theorem rec1250 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[81]? = some (⟨23,(8),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1251 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[82]? = some (⟨23,(8),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1254 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[85]? = some (⟨23,(8),[1,13],[151],2⟩) from rfl))
private theorem rec1257 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[88]? = some (⟨23,(9),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1258 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[89]? = some (⟨23,(9),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1261 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[92]? = some (⟨23,(9),[1,13],[151],2⟩) from rfl))
private theorem rec1264 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[95]? = some (⟨23,(10),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1265 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[96]? = some (⟨23,(10),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1268 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[99]? = some (⟨23,(10),[1,13],[151],2⟩) from rfl))
private theorem rec1271 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[102]? = some (⟨23,(11),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1272 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[103]? = some (⟨23,(11),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1275 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[106]? = some (⟨23,(11),[1,13],[151],2⟩) from rfl))
private theorem rec1278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[109]? = some (⟨23,(12),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1279 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[110]? = some (⟨23,(12),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1282 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[113]? = some (⟨23,(12),[1,13],[151],2⟩) from rfl))
private theorem rec1285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[116]? = some (⟨23,(13),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1286 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[117]? = some (⟨23,(13),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1289 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[120]? = some (⟨23,(13),[1,13],[151],2⟩) from rfl))
private theorem rec1292 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[123]? = some (⟨23,(14),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1293 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[124]? = some (⟨23,(14),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1296 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[127]? = some (⟨23,(14),[1,13],[151],2⟩) from rfl))
private theorem rec1299 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[130]? = some (⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1300 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[131]? = some (⟨23,(15),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1303 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[134]? = some (⟨23,(15),[1,13],[151],2⟩) from rfl))
private theorem rec1306 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[137]? = some (⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1307 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[138]? = some (⟨23,(16),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1310 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[141]? = some (⟨23,(16),[1,13],[151],2⟩) from rfl))
private theorem rec1313 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[144]? = some (⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1314 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[145]? = some (⟨23,(17),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1317 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[148]? = some (⟨23,(17),[1,13],[151],2⟩) from rfl))
private theorem rec1320 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[151]? = some (⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1321 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[152]? = some (⟨23,(18),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1324 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[155]? = some (⟨23,(18),[1,13],[151],2⟩) from rfl))
private theorem rec1327 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[158]? = some (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1328 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[159]? = some (⟨23,(19),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1331 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[162]? = some (⟨23,(19),[1,13],[151],2⟩) from rfl))
private theorem rec1334 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[165]? = some (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1335 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[166]? = some (⟨23,(20),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1338 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[169]? = some (⟨23,(20),[1,13],[151],2⟩) from rfl))
private theorem rec1341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[172]? = some (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1342 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[173]? = some (⟨23,(21),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1345 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[176]? = some (⟨23,(21),[1,13],[151],2⟩) from rfl))
private theorem rec1348 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[179]? = some (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1349 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[180]? = some (⟨23,(22),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1352 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[183]? = some (⟨23,(22),[1,13],[151],2⟩) from rfl))
private theorem rec1355 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[186]? = some (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1356 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[187]? = some (⟨23,(23),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1359 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[190]? = some (⟨23,(23),[1,13],[151],2⟩) from rfl))
private theorem rec1362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[193]? = some (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1363 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[194]? = some (⟨23,(24),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1366 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[197]? = some (⟨23,(24),[1,13],[151],2⟩) from rfl))
private theorem rec1369 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,2,5,6,13,14],[146],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[200]? = some (⟨25,(0),[1,2,5,6,13,14],[146],145⟩) from rfl))
private theorem rec1370 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,2,5,6,13,14],[150],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[201]? = some (⟨25,(0),[1,2,5,6,13,14],[150],189⟩) from rfl))
private theorem rec1372 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,2,13,14],[147],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[203]? = some (⟨25,(0),[1,2,13,14],[147],167⟩) from rfl))
private theorem rec1376 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,13],[151],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[207]? = some (⟨25,(0),[1,13],[151],167⟩) from rfl))
private theorem rec1390 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,2,5,6,13,14],[146],146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[221]? = some (⟨25,(1),[1,2,5,6,13,14],[146],146⟩) from rfl))
private theorem rec1392 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,2,13,14],[147],168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[223]? = some (⟨25,(1),[1,2,13,14],[147],168⟩) from rfl))
private theorem rec1393 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,2,13,14],[150],190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[224]? = some (⟨25,(1),[1,2,13,14],[150],190⟩) from rfl))
private theorem rec1397 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,13],[151],168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[228]? = some (⟨25,(1),[1,13],[151],168⟩) from rfl))
private theorem rec1414 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,2,5,6,13,14],[146],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[245]? = some (⟨25,(2),[1,2,5,6,13,14],[146],145⟩) from rfl))
private theorem rec1416 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,2,13,14],[147],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[247]? = some (⟨25,(2),[1,2,13,14],[147],167⟩) from rfl))
private theorem rec1417 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,2,13,14],[150],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[248]? = some (⟨25,(2),[1,2,13,14],[150],191⟩) from rfl))
private theorem rec1421 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,13],[151],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[252]? = some (⟨25,(2),[1,13],[151],167⟩) from rfl))
private theorem rec1438 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,2,5,6,13,14],[146],147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[269]? = some (⟨25,(3),[1,2,5,6,13,14],[146],147⟩) from rfl))
private theorem rec1440 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,2,13,14],[147],169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[271]? = some (⟨25,(3),[1,2,13,14],[147],169⟩) from rfl))
private theorem rec1441 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,2,13,14],[150],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[272]? = some (⟨25,(3),[1,2,13,14],[150],192⟩) from rfl))
private theorem rec1445 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,13],[151],169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[276]? = some (⟨25,(3),[1,13],[151],169⟩) from rfl))
private theorem rec1462 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,2,5,6,13,14],[146],148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[293]? = some (⟨25,(4),[1,2,5,6,13,14],[146],148⟩) from rfl))
private theorem rec1464 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,2,13,14],[147],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[295]? = some (⟨25,(4),[1,2,13,14],[147],170⟩) from rfl))
private theorem rec1465 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,2,13,14],[150],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[296]? = some (⟨25,(4),[1,2,13,14],[150],193⟩) from rfl))
private theorem rec1469 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,13],[151],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[300]? = some (⟨25,(4),[1,13],[151],170⟩) from rfl))
private theorem rec1486 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,2,5,6,13,14],[146],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[317]? = some (⟨25,(5),[1,2,5,6,13,14],[146],145⟩) from rfl))
private theorem rec1487 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,2,5,6,13,14],[150],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[318]? = some (⟨25,(5),[1,2,5,6,13,14],[150],189⟩) from rfl))
private theorem rec1489 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,2,13,14],[147],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[320]? = some (⟨25,(5),[1,2,13,14],[147],167⟩) from rfl))
private theorem rec1493 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,13],[151],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[324]? = some (⟨25,(5),[1,13],[151],167⟩) from rfl))
private theorem rec1507 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,2,5,6,13,14],[146],146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[338]? = some (⟨25,(6),[1,2,5,6,13,14],[146],146⟩) from rfl))
private theorem rec1509 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,2,13,14],[147],168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[340]? = some (⟨25,(6),[1,2,13,14],[147],168⟩) from rfl))
private theorem rec1510 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,2,13,14],[150],190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[341]? = some (⟨25,(6),[1,2,13,14],[150],190⟩) from rfl))
private theorem rec1514 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,13],[151],168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[345]? = some (⟨25,(6),[1,13],[151],168⟩) from rfl))
private theorem rec1531 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,2,5,6,13,14],[146],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[362]? = some (⟨25,(7),[1,2,5,6,13,14],[146],145⟩) from rfl))
private theorem rec1533 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,2,13,14],[147],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[364]? = some (⟨25,(7),[1,2,13,14],[147],167⟩) from rfl))
private theorem rec1534 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,2,13,14],[150],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[365]? = some (⟨25,(7),[1,2,13,14],[150],191⟩) from rfl))
private theorem rec1538 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,13],[151],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[369]? = some (⟨25,(7),[1,13],[151],167⟩) from rfl))
private theorem rec1555 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,2,5,6,13,14],[146],147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[386]? = some (⟨25,(8),[1,2,5,6,13,14],[146],147⟩) from rfl))
private theorem rec1557 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,2,13,14],[147],169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[388]? = some (⟨25,(8),[1,2,13,14],[147],169⟩) from rfl))
private theorem rec1558 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,2,13,14],[150],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[389]? = some (⟨25,(8),[1,2,13,14],[150],192⟩) from rfl))
private theorem rec1562 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,13],[151],169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[393]? = some (⟨25,(8),[1,13],[151],169⟩) from rfl))
private theorem rec1579 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,2,5,6,13,14],[146],148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[410]? = some (⟨25,(9),[1,2,5,6,13,14],[146],148⟩) from rfl))
private theorem rec1581 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,2,13,14],[147],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[412]? = some (⟨25,(9),[1,2,13,14],[147],170⟩) from rfl))
private theorem rec1582 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,2,13,14],[150],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[413]? = some (⟨25,(9),[1,2,13,14],[150],193⟩) from rfl))
private theorem rec1586 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,13],[151],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[417]? = some (⟨25,(9),[1,13],[151],170⟩) from rfl))
private theorem rec1603 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,2,5,6,13,14],[146],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[434]? = some (⟨25,(10),[1,2,5,6,13,14],[146],149⟩) from rfl))
private theorem rec1604 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,2,5,6,13,14],[150],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[435]? = some (⟨25,(10),[1,2,5,6,13,14],[150],194⟩) from rfl))
private theorem rec1606 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,2,13,14],[147],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[437]? = some (⟨25,(10),[1,2,13,14],[147],171⟩) from rfl))
private theorem rec1610 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,13],[151],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[441]? = some (⟨25,(10),[1,13],[151],171⟩) from rfl))
private theorem rec1624 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,2,5,6,13,14],[146],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[455]? = some (⟨25,(11),[1,2,5,6,13,14],[146],149⟩) from rfl))
private theorem rec1626 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,2,13,14],[147],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[457]? = some (⟨25,(11),[1,2,13,14],[147],171⟩) from rfl))
private theorem rec1627 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,2,13,14],[150],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[458]? = some (⟨25,(11),[1,2,13,14],[150],195⟩) from rfl))
private theorem rec1631 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,13],[151],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[462]? = some (⟨25,(11),[1,13],[151],171⟩) from rfl))
private theorem rec1648 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,2,5,6,13,14],[146],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[479]? = some (⟨25,(12),[1,2,5,6,13,14],[146],149⟩) from rfl))
private theorem rec1650 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,2,13,14],[147],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[481]? = some (⟨25,(12),[1,2,13,14],[147],171⟩) from rfl))
private theorem rec1651 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,2,13,14],[150],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[482]? = some (⟨25,(12),[1,2,13,14],[150],195⟩) from rfl))
private theorem rec1655 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,13],[151],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[486]? = some (⟨25,(12),[1,13],[151],171⟩) from rfl))
private theorem rec1672 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,2,5,6,13,14],[146],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[503]? = some (⟨25,(13),[1,2,5,6,13,14],[146],149⟩) from rfl))
private theorem rec1674 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,2,13,14],[147],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[505]? = some (⟨25,(13),[1,2,13,14],[147],171⟩) from rfl))
private theorem rec1675 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,2,13,14],[150],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[506]? = some (⟨25,(13),[1,2,13,14],[150],195⟩) from rfl))
private theorem rec1679 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,13],[151],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[510]? = some (⟨25,(13),[1,13],[151],171⟩) from rfl))
private theorem rec1696 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,2,5,6,13,14],[146],148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[527]? = some (⟨25,(14),[1,2,5,6,13,14],[146],148⟩) from rfl))
private theorem rec1698 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,2,13,14],[147],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[529]? = some (⟨25,(14),[1,2,13,14],[147],170⟩) from rfl))
private theorem rec1699 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,2,13,14],[150],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[530]? = some (⟨25,(14),[1,2,13,14],[150],193⟩) from rfl))
private theorem rec1703 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,13],[151],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[534]? = some (⟨25,(14),[1,13],[151],170⟩) from rfl))
private theorem rec1720 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,2,5,6,13,14],[146],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[551]? = some (⟨25,(15),[1,2,5,6,13,14],[146],150⟩) from rfl))
private theorem rec1721 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,2,5,6,13,14],[150],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[552]? = some (⟨25,(15),[1,2,5,6,13,14],[150],196⟩) from rfl))
private theorem rec1723 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,2,13,14],[147],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[554]? = some (⟨25,(15),[1,2,13,14],[147],172⟩) from rfl))
private theorem rec1727 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,13],[151],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[558]? = some (⟨25,(15),[1,13],[151],172⟩) from rfl))
private theorem rec1741 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,2,5,6,13,14],[146],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[572]? = some (⟨25,(16),[1,2,5,6,13,14],[146],150⟩) from rfl))
private theorem rec1743 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,2,13,14],[147],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[574]? = some (⟨25,(16),[1,2,13,14],[147],172⟩) from rfl))
private theorem rec1744 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,2,13,14],[150],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[575]? = some (⟨25,(16),[1,2,13,14],[150],197⟩) from rfl))
private theorem rec1748 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,13],[151],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[579]? = some (⟨25,(16),[1,13],[151],172⟩) from rfl))
private theorem rec1765 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,2,5,6,13,14],[146],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[596]? = some (⟨25,(17),[1,2,5,6,13,14],[146],150⟩) from rfl))
private theorem rec1767 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,2,13,14],[147],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[598]? = some (⟨25,(17),[1,2,13,14],[147],172⟩) from rfl))
private theorem rec1768 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,2,13,14],[150],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[599]? = some (⟨25,(17),[1,2,13,14],[150],197⟩) from rfl))
private theorem rec1772 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,13],[151],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[603]? = some (⟨25,(17),[1,13],[151],172⟩) from rfl))
private theorem rec1789 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,2,5,6,13,14],[146],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[620]? = some (⟨25,(18),[1,2,5,6,13,14],[146],150⟩) from rfl))
private theorem rec1791 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,2,13,14],[147],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[622]? = some (⟨25,(18),[1,2,13,14],[147],172⟩) from rfl))
private theorem rec1792 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,2,13,14],[150],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[623]? = some (⟨25,(18),[1,2,13,14],[150],197⟩) from rfl))
private theorem rec1796 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,13],[151],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[627]? = some (⟨25,(18),[1,13],[151],172⟩) from rfl))
private theorem rec1813 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,2,5,6,13,14],[146],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[644]? = some (⟨25,(19),[1,2,5,6,13,14],[146],150⟩) from rfl))
private theorem rec1815 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,2,13,14],[147],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[646]? = some (⟨25,(19),[1,2,13,14],[147],172⟩) from rfl))
private theorem rec1816 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,2,13,14],[150],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[647]? = some (⟨25,(19),[1,2,13,14],[150],197⟩) from rfl))
private theorem rec1820 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,13],[151],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[651]? = some (⟨25,(19),[1,13],[151],172⟩) from rfl))
private theorem rec1837 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,2,5,6,13,14],[146],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[668]? = some (⟨25,(20),[1,2,5,6,13,14],[146],151⟩) from rfl))
private theorem rec1838 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,2,5,6,13,14],[150],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[669]? = some (⟨25,(20),[1,2,5,6,13,14],[150],198⟩) from rfl))
private theorem rec1840 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,2,13,14],[147],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[671]? = some (⟨25,(20),[1,2,13,14],[147],173⟩) from rfl))
private theorem rec1844 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,13],[151],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[675]? = some (⟨25,(20),[1,13],[151],173⟩) from rfl))
private theorem rec1858 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,2,5,6,13,14],[146],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[689]? = some (⟨25,(21),[1,2,5,6,13,14],[146],151⟩) from rfl))
private theorem rec1860 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,2,13,14],[147],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[691]? = some (⟨25,(21),[1,2,13,14],[147],173⟩) from rfl))
private theorem rec1861 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,2,13,14],[150],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[692]? = some (⟨25,(21),[1,2,13,14],[150],199⟩) from rfl))
private theorem rec1865 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,13],[151],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[696]? = some (⟨25,(21),[1,13],[151],173⟩) from rfl))
private theorem rec1882 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,2,5,6,13,14],[146],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[713]? = some (⟨25,(22),[1,2,5,6,13,14],[146],151⟩) from rfl))
private theorem rec1884 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,2,13,14],[147],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[715]? = some (⟨25,(22),[1,2,13,14],[147],173⟩) from rfl))
private theorem rec1885 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,2,13,14],[150],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[716]? = some (⟨25,(22),[1,2,13,14],[150],199⟩) from rfl))
private theorem rec1889 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,13],[151],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[720]? = some (⟨25,(22),[1,13],[151],173⟩) from rfl))
private theorem rec1906 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,2,5,6,13,14],[146],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[737]? = some (⟨25,(23),[1,2,5,6,13,14],[146],151⟩) from rfl))
private theorem rec1908 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,2,13,14],[147],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[739]? = some (⟨25,(23),[1,2,13,14],[147],173⟩) from rfl))
private theorem rec1909 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,2,13,14],[150],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[740]? = some (⟨25,(23),[1,2,13,14],[150],199⟩) from rfl))
private theorem rec1913 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,13],[151],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[744]? = some (⟨25,(23),[1,13],[151],173⟩) from rfl))
private theorem rec1930 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,2,5,6,13,14],[146],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[761]? = some (⟨25,(24),[1,2,5,6,13,14],[146],151⟩) from rfl))
private theorem rec1932 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,2,13,14],[147],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[763]? = some (⟨25,(24),[1,2,13,14],[147],173⟩) from rfl))
private theorem rec1933 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,2,13,14],[150],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[764]? = some (⟨25,(24),[1,2,13,14],[150],199⟩) from rfl))
private theorem rec1937 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,13],[151],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[768]? = some (⟨25,(24),[1,13],[151],173⟩) from rfl))
private theorem rec1953 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1],[146],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[784]? = some (⟨28,(0),[1],[146],85⟩) from rfl))
private theorem rec1954 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1],[151],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[785]? = some (⟨28,(0),[1],[151],132⟩) from rfl))
private theorem rec1955 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1],[147],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[786]? = some (⟨28,(0),[1],[147],174⟩) from rfl))
private theorem rec1958 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[789]? = some (⟨28,(0),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec1969 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1],[146],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[800]? = some (⟨28,(1),[1],[146],85⟩) from rfl))
private theorem rec1970 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1],[151],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[801]? = some (⟨28,(1),[1],[151],132⟩) from rfl))
private theorem rec1971 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1],[147],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[802]? = some (⟨28,(1),[1],[147],174⟩) from rfl))
private theorem rec1974 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[805]? = some (⟨28,(1),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec1985 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1],[146],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[816]? = some (⟨28,(2),[1],[146],85⟩) from rfl))
private theorem rec1986 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1],[151],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[817]? = some (⟨28,(2),[1],[151],132⟩) from rfl))
private theorem rec1987 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1],[147],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[818]? = some (⟨28,(2),[1],[147],174⟩) from rfl))
private theorem rec1990 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[821]? = some (⟨28,(2),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec2001 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1],[146],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[832]? = some (⟨28,(3),[1],[146],85⟩) from rfl))
private theorem rec2002 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1],[151],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[833]? = some (⟨28,(3),[1],[151],132⟩) from rfl))
private theorem rec2003 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1],[147],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[834]? = some (⟨28,(3),[1],[147],174⟩) from rfl))
private theorem rec2006 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[837]? = some (⟨28,(3),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec2017 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1],[146],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[848]? = some (⟨28,(4),[1],[146],85⟩) from rfl))
private theorem rec2018 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1],[151],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[849]? = some (⟨28,(4),[1],[151],132⟩) from rfl))
private theorem rec2019 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1],[147],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[850]? = some (⟨28,(4),[1],[147],174⟩) from rfl))
private theorem rec2022 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[853]? = some (⟨28,(4),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec2033 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1],[146],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[864]? = some (⟨28,(5),[1],[146],86⟩) from rfl))
private theorem rec2034 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1],[151],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[865]? = some (⟨28,(5),[1],[151],133⟩) from rfl))
private theorem rec2035 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1],[147],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[866]? = some (⟨28,(5),[1],[147],175⟩) from rfl))
private theorem rec2038 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[869]? = some (⟨28,(5),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2049 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1],[146],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[880]? = some (⟨28,(6),[1],[146],86⟩) from rfl))
private theorem rec2050 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1],[151],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[881]? = some (⟨28,(6),[1],[151],133⟩) from rfl))
private theorem rec2051 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1],[147],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[882]? = some (⟨28,(6),[1],[147],175⟩) from rfl))
private theorem rec2054 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[885]? = some (⟨28,(6),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2065 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1],[146],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[896]? = some (⟨28,(7),[1],[146],86⟩) from rfl))
private theorem rec2066 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1],[151],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[897]? = some (⟨28,(7),[1],[151],133⟩) from rfl))
private theorem rec2067 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1],[147],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[898]? = some (⟨28,(7),[1],[147],175⟩) from rfl))
private theorem rec2070 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[901]? = some (⟨28,(7),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2081 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1],[146],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[912]? = some (⟨28,(8),[1],[146],86⟩) from rfl))
private theorem rec2082 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1],[151],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[913]? = some (⟨28,(8),[1],[151],133⟩) from rfl))
private theorem rec2083 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1],[147],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[914]? = some (⟨28,(8),[1],[147],175⟩) from rfl))
private theorem rec2086 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[917]? = some (⟨28,(8),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2097 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1],[146],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[928]? = some (⟨28,(9),[1],[146],86⟩) from rfl))
private theorem rec2098 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1],[151],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[929]? = some (⟨28,(9),[1],[151],133⟩) from rfl))
private theorem rec2099 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1],[147],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[930]? = some (⟨28,(9),[1],[147],175⟩) from rfl))
private theorem rec2102 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[933]? = some (⟨28,(9),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2113 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1],[146],87⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[944]? = some (⟨28,(10),[1],[146],87⟩) from rfl))
private theorem rec2114 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1],[151],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[945]? = some (⟨28,(10),[1],[151],134⟩) from rfl))
private theorem rec2115 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1],[147],176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[946]? = some (⟨28,(10),[1],[147],176⟩) from rfl))
private theorem rec2118 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1,2,5,6],[150],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[949]? = some (⟨28,(10),[1,2,5,6],[150],134⟩) from rfl))
private theorem rec2129 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1],[146],88⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[960]? = some (⟨28,(11),[1],[146],88⟩) from rfl))
private theorem rec2130 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1],[151],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[961]? = some (⟨28,(11),[1],[151],135⟩) from rfl))
private theorem rec2131 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1],[147],177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[962]? = some (⟨28,(11),[1],[147],177⟩) from rfl))
private theorem rec2134 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1,2,5,6],[150],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[965]? = some (⟨28,(11),[1,2,5,6],[150],135⟩) from rfl))
private theorem rec2145 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1],[146],89⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[976]? = some (⟨28,(12),[1],[146],89⟩) from rfl))
private theorem rec2146 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1],[151],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[977]? = some (⟨28,(12),[1],[151],136⟩) from rfl))
private theorem rec2147 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1],[147],178⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[978]? = some (⟨28,(12),[1],[147],178⟩) from rfl))
private theorem rec2150 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1,2,5,6],[150],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[981]? = some (⟨28,(12),[1,2,5,6],[150],136⟩) from rfl))
private theorem rec2161 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1],[146],88⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[992]? = some (⟨28,(13),[1],[146],88⟩) from rfl))
private theorem rec2162 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1],[151],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[993]? = some (⟨28,(13),[1],[151],135⟩) from rfl))
private theorem rec2163 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1],[147],177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[994]? = some (⟨28,(13),[1],[147],177⟩) from rfl))
private theorem rec2166 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1,2,5,6],[150],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[997]? = some (⟨28,(13),[1,2,5,6],[150],135⟩) from rfl))
private theorem rec2177 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1],[146],90⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1008]? = some (⟨28,(14),[1],[146],90⟩) from rfl))
private theorem rec2178 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1],[151],137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1009]? = some (⟨28,(14),[1],[151],137⟩) from rfl))
private theorem rec2179 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1],[147],179⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1010]? = some (⟨28,(14),[1],[147],179⟩) from rfl))
private theorem rec2182 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1,2,5,6],[150],137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1013]? = some (⟨28,(14),[1,2,5,6],[150],137⟩) from rfl))
private theorem rec2193 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1],[146],87⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1024]? = some (⟨28,(15),[1],[146],87⟩) from rfl))
private theorem rec2194 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1],[151],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1025]? = some (⟨28,(15),[1],[151],134⟩) from rfl))
private theorem rec2195 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1],[147],176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1026]? = some (⟨28,(15),[1],[147],176⟩) from rfl))
private theorem rec2198 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1,2,5,6],[150],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1029]? = some (⟨28,(15),[1,2,5,6],[150],134⟩) from rfl))
private theorem rec2209 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1],[146],91⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1040]? = some (⟨28,(16),[1],[146],91⟩) from rfl))
private theorem rec2210 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1],[151],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1041]? = some (⟨28,(16),[1],[151],138⟩) from rfl))
private theorem rec2211 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1],[147],180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1042]? = some (⟨28,(16),[1],[147],180⟩) from rfl))
private theorem rec2214 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1,2,5,6],[150],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1045]? = some (⟨28,(16),[1,2,5,6],[150],138⟩) from rfl))
private theorem rec2225 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1],[146],91⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1056]? = some (⟨28,(17),[1],[146],91⟩) from rfl))
private theorem rec2226 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1],[151],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1057]? = some (⟨28,(17),[1],[151],138⟩) from rfl))
private theorem rec2227 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1],[147],180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1058]? = some (⟨28,(17),[1],[147],180⟩) from rfl))
private theorem rec2230 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1,2,5,6],[150],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1061]? = some (⟨28,(17),[1,2,5,6],[150],138⟩) from rfl))
private theorem rec2241 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1],[146],91⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1072]? = some (⟨28,(18),[1],[146],91⟩) from rfl))
private theorem rec2242 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1],[151],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1073]? = some (⟨28,(18),[1],[151],138⟩) from rfl))
private theorem rec2243 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1],[147],180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1074]? = some (⟨28,(18),[1],[147],180⟩) from rfl))
private theorem rec2246 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1,2,5,6],[150],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1077]? = some (⟨28,(18),[1,2,5,6],[150],138⟩) from rfl))
private theorem rec2257 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1],[146],91⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1088]? = some (⟨28,(19),[1],[146],91⟩) from rfl))
private theorem rec2258 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1],[151],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1089]? = some (⟨28,(19),[1],[151],138⟩) from rfl))
private theorem rec2259 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1],[147],180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1090]? = some (⟨28,(19),[1],[147],180⟩) from rfl))
private theorem rec2262 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1,2,5,6],[150],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1093]? = some (⟨28,(19),[1,2,5,6],[150],138⟩) from rfl))
private theorem rec2273 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1],[146],87⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1104]? = some (⟨28,(20),[1],[146],87⟩) from rfl))
private theorem rec2274 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1],[151],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1105]? = some (⟨28,(20),[1],[151],134⟩) from rfl))
private theorem rec2275 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1],[147],176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1106]? = some (⟨28,(20),[1],[147],176⟩) from rfl))
private theorem rec2278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1,2,5,6],[150],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1109]? = some (⟨28,(20),[1,2,5,6],[150],134⟩) from rfl))
private theorem rec2289 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1],[146],88⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1120]? = some (⟨28,(21),[1],[146],88⟩) from rfl))
private theorem rec2290 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1],[151],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1121]? = some (⟨28,(21),[1],[151],135⟩) from rfl))
private theorem rec2291 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1],[147],177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1122]? = some (⟨28,(21),[1],[147],177⟩) from rfl))
private theorem rec2294 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1,2,5,6],[150],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1125]? = some (⟨28,(21),[1,2,5,6],[150],135⟩) from rfl))
private theorem rec2305 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1],[146],89⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1136]? = some (⟨28,(22),[1],[146],89⟩) from rfl))
private theorem rec2306 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1],[151],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1137]? = some (⟨28,(22),[1],[151],136⟩) from rfl))
private theorem rec2307 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1],[147],178⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1138]? = some (⟨28,(22),[1],[147],178⟩) from rfl))
private theorem rec2310 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1,2,5,6],[150],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1141]? = some (⟨28,(22),[1,2,5,6],[150],136⟩) from rfl))
private theorem rec2321 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1],[146],88⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1152]? = some (⟨28,(23),[1],[146],88⟩) from rfl))
private theorem rec2322 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1],[151],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1153]? = some (⟨28,(23),[1],[151],135⟩) from rfl))
private theorem rec2323 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1],[147],177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1154]? = some (⟨28,(23),[1],[147],177⟩) from rfl))
private theorem rec2326 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1,2,5,6],[150],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1157]? = some (⟨28,(23),[1,2,5,6],[150],135⟩) from rfl))
private theorem rec2337 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1],[146],90⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1168]? = some (⟨28,(24),[1],[146],90⟩) from rfl))
private theorem rec2338 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1],[151],137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1169]? = some (⟨28,(24),[1],[151],137⟩) from rfl))
private theorem rec2339 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1],[147],179⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1170]? = some (⟨28,(24),[1],[147],179⟩) from rfl))
private theorem rec2342 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1,2,5,6],[150],137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1173]? = some (⟨28,(24),[1,2,5,6],[150],137⟩) from rfl))
private theorem rec2354 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([135, 151] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[1],[135,151],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1185]? = some (⟨30,(0),[1],[135,151],120⟩) from rfl))
private theorem rec2356 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[1,2],[147],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1187]? = some (⟨30,(0),[1,2],[147],120⟩) from rfl))
private theorem rec2358 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[1,2,5,6],[146,150],152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1189]? = some (⟨30,(0),[1,2,5,6],[146,150],152⟩) from rfl))
private theorem rec2370 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[1],[151],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1201]? = some (⟨30,(1),[1],[151],181⟩) from rfl))
private theorem rec2373 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[1,2],[147],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1204]? = some (⟨30,(1),[1,2],[147],181⟩) from rfl))
private theorem rec2374 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[1,2,5,6],[146,150],153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1205]? = some (⟨30,(1),[1,2,5,6],[146,150],153⟩) from rfl))
private theorem rec2384 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1],[151],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1215]? = some (⟨30,(2),[1],[151],120⟩) from rfl))
private theorem rec2385 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,2],[147],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1216]? = some (⟨30,(2),[1,2],[147],120⟩) from rfl))
private theorem rec2388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,2,5,6],[146],154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1219]? = some (⟨30,(2),[1,2,5,6],[146],154⟩) from rfl))
private theorem rec2389 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,2,5,6],[150],200⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1220]? = some (⟨30,(2),[1,2,5,6],[150],200⟩) from rfl))
private theorem rec2405 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1],[151],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1236]? = some (⟨30,(3),[1],[151],181⟩) from rfl))
private theorem rec2407 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1,2],[147],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1238]? = some (⟨30,(3),[1,2],[147],181⟩) from rfl))
private theorem rec2408 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1,2],[150],201⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1239]? = some (⟨30,(3),[1,2],[150],201⟩) from rfl))
private theorem rec2411 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1,2,5,6],[146],155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1242]? = some (⟨30,(3),[1,2,5,6],[146],155⟩) from rfl))
private theorem rec2429 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1],[151],182⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1260]? = some (⟨30,(4),[1],[151],182⟩) from rfl))
private theorem rec2431 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1,2],[147],182⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1262]? = some (⟨30,(4),[1,2],[147],182⟩) from rfl))
private theorem rec2432 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1,2],[150],202⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1263]? = some (⟨30,(4),[1,2],[150],202⟩) from rfl))
private theorem rec2435 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1,2,5,6],[146],156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1266]? = some (⟨30,(4),[1,2,5,6],[146],156⟩) from rfl))
private theorem rec2453 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1],[151],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[10]? = some (⟨30,(5),[1],[151],181⟩) from rfl))
private theorem rec2455 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1,2],[147],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[12]? = some (⟨30,(5),[1,2],[147],181⟩) from rfl))
private theorem rec2456 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1,2],[150],201⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[13]? = some (⟨30,(5),[1,2],[150],201⟩) from rfl))
private theorem rec2459 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1,2,5,6],[146],155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[16]? = some (⟨30,(5),[1,2,5,6],[146],155⟩) from rfl))
private theorem rec2477 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1],[151],183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[34]? = some (⟨30,(6),[1],[151],183⟩) from rfl))
private theorem rec2479 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1,2],[147],183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[36]? = some (⟨30,(6),[1,2],[147],183⟩) from rfl))
private theorem rec2480 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1,2],[150],203⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[37]? = some (⟨30,(6),[1,2],[150],203⟩) from rfl))
private theorem rec2483 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1,2,5,6],[146],157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[40]? = some (⟨30,(6),[1,2,5,6],[146],157⟩) from rfl))
private theorem rec2501 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1],[151],183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[58]? = some (⟨30,(7),[1],[151],183⟩) from rfl))
private theorem rec2503 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1,2],[147],183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[60]? = some (⟨30,(7),[1,2],[147],183⟩) from rfl))
private theorem rec2504 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1,2],[150],203⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[61]? = some (⟨30,(7),[1,2],[150],203⟩) from rfl))
private theorem rec2507 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1,2,5,6],[146],157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[64]? = some (⟨30,(7),[1,2,5,6],[146],157⟩) from rfl))
private theorem rec2525 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1],[151],184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[82]? = some (⟨30,(8),[1],[151],184⟩) from rfl))
private theorem rec2527 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1,2],[147],184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[84]? = some (⟨30,(8),[1,2],[147],184⟩) from rfl))
private theorem rec2528 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1,2],[150],204⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[85]? = some (⟨30,(8),[1,2],[150],204⟩) from rfl))
private theorem rec2531 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1,2,5,6],[146],158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[88]? = some (⟨30,(8),[1,2,5,6],[146],158⟩) from rfl))
private theorem rec2549 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1],[151],184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[106]? = some (⟨30,(9),[1],[151],184⟩) from rfl))
private theorem rec2551 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1,2],[147],184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[108]? = some (⟨30,(9),[1,2],[147],184⟩) from rfl))
private theorem rec2552 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1,2],[150],204⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[109]? = some (⟨30,(9),[1,2],[150],204⟩) from rfl))
private theorem rec2555 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1,2,5,6],[146],158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[112]? = some (⟨30,(9),[1,2,5,6],[146],158⟩) from rfl))
private theorem rec2572 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147, 151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[1],[147,151],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[129]? = some (⟨33,(0),[1],[147,151],98⟩) from rfl))
private theorem rec2576 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[1,5,6],[146,150],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[133]? = some (⟨33,(0),[1,5,6],[146,150],98⟩) from rfl))
private theorem rec2586 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([146, 147, 150, 151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(1),[1,13],[146,147,150,151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[143]? = some (⟨33,(1),[1,13],[146,147,150,151],2⟩) from rfl))
private theorem rec2598 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(2),[1,5,6,13,14],[146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[155]? = some (⟨33,(2),[1,5,6,13,14],[146,150],3⟩) from rfl))
private theorem rec2599 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(2),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[156]? = some (⟨33,(2),[1,13],[151],3⟩) from rfl))
private theorem rec2600 (si parent : ℕ) (hs : si ∈ ([1, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(2),[1,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[157]? = some (⟨33,(2),[1,13,14],[147],3⟩) from rfl))
private theorem rec2612 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[169]? = some (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2614 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[171]? = some (⟨33,(3),[1,13],[151],3⟩) from rfl))
private theorem rec2615 (si parent : ℕ) (hs : si ∈ ([1, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[172]? = some (⟨33,(3),[1,13,14],[147],3⟩) from rfl))
private theorem rec2620 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147, 151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1],[147,151],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[177]? = some (⟨33,(4),[1],[147,151],98⟩) from rfl))
private theorem rec2624 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,5,6],[146,150],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[181]? = some (⟨33,(4),[1,5,6],[146,150],98⟩) from rfl))
private theorem rec2633 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[1,2,5,6,13,14],[146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[190]? = some (⟨33,(5),[1,2,5,6,13,14],[146,150],2⟩) from rfl))
private theorem rec2634 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[1,2,13,14],[147],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[191]? = some (⟨33,(5),[1,2,13,14],[147],2⟩) from rfl))
private theorem rec2637 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[1,13],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[194]? = some (⟨33,(5),[1,13],[151],2⟩) from rfl))
private theorem rec2648 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[205]? = some (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2650 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[207]? = some (⟨33,(6),[1,13],[151],3⟩) from rfl))
private theorem rec2651 (si parent : ℕ) (hs : si ∈ ([1, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[208]? = some (⟨33,(6),[1,13,14],[147],3⟩) from rfl))
private theorem rec2659 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[216]? = some (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2661 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[218]? = some (⟨33,(7),[1,13],[151],3⟩) from rfl))
private theorem rec2662 (si parent : ℕ) (hs : si ∈ ([1, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[219]? = some (⟨33,(7),[1,13,14],[147],3⟩) from rfl))
private theorem rec2668 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,2,5,6,13,14],[146,150],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[225]? = some (⟨33,(8),[1,2,5,6,13,14],[146,150],98⟩) from rfl))
private theorem rec2670 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,2,13,14],[147],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[227]? = some (⟨33,(8),[1,2,13,14],[147],98⟩) from rfl))
private theorem rec2673 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,13],[151],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[230]? = some (⟨33,(8),[1,13],[151],98⟩) from rfl))
private theorem rec2678 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,2,5,6,13,14],[146,150],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[235]? = some (⟨33,(9),[1,2,5,6,13,14],[146,150],159⟩) from rfl))
private theorem rec2680 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,2,13,14],[147],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[237]? = some (⟨33,(9),[1,2,13,14],[147],159⟩) from rfl))
private theorem rec2683 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,13],[151],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[240]? = some (⟨33,(9),[1,13],[151],159⟩) from rfl))
private theorem rec2688 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[1,2,5,6,13,14],[146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[245]? = some (⟨33,(10),[1,2,5,6,13,14],[146,150],3⟩) from rfl))
private theorem rec2689 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[246]? = some (⟨33,(10),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec2691 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[248]? = some (⟨33,(10),[1,13],[151],3⟩) from rfl))
private theorem rec2698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[255]? = some (⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2699 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,2,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[256]? = some (⟨33,(11),[1,2,13,14],[147],3⟩) from rfl))
private theorem rec2703 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[260]? = some (⟨33,(11),[1,13],[151],3⟩) from rfl))
private theorem rec2705 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1],[151],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[262]? = some (⟨33,(12),[1],[151],99⟩) from rfl))
private theorem rec2706 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,2],[147],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[263]? = some (⟨33,(12),[1,2],[147],99⟩) from rfl))
private theorem rec2707 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,2,5,6],[130,146,150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[264]? = some (⟨33,(12),[1,2,5,6],[130,146,150],99⟩) from rfl))
private theorem rec2719 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(13),[1,2,5,6,13,14],[146,150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[276]? = some (⟨33,(13),[1,2,5,6,13,14],[146,150],99⟩) from rfl))
private theorem rec2720 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(13),[1,2,13,14],[147],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[277]? = some (⟨33,(13),[1,2,13,14],[147],99⟩) from rfl))
private theorem rec2723 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(13),[1,13],[151],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[280]? = some (⟨33,(13),[1,13],[151],99⟩) from rfl))
private theorem rec2730 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[1],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[287]? = some (⟨33,(14),[1],[151],3⟩) from rfl))
private theorem rec2732 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[1,2,5,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[289]? = some (⟨33,(14),[1,2,5,14],[131,146,150],3⟩) from rfl))
private theorem rec2734 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[1,2,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[291]? = some (⟨33,(14),[1,2,14],[147],3⟩) from rfl))
private theorem rec2741 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[1],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[298]? = some (⟨33,(15),[1],[151],3⟩) from rfl))
private theorem rec2743 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[1,2,5,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[300]? = some (⟨33,(15),[1,2,5,14],[131,146,150],3⟩) from rfl))
private theorem rec2745 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[1,2,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[302]? = some (⟨33,(15),[1,2,14],[147],3⟩) from rfl))
private theorem rec2751 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(0),[1],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[308]? = some (⟨35,(0),[1],[151],2⟩) from rfl))
private theorem rec2752 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(0),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[309]? = some (⟨35,(0),[1,2],[147,190],2⟩) from rfl))
private theorem rec2753 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[310]? = some (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2756 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(1),[1],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[313]? = some (⟨35,(1),[1],[151],2⟩) from rfl))
private theorem rec2757 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(1),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[314]? = some (⟨35,(1),[1,2],[147,190],2⟩) from rfl))
private theorem rec2758 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[315]? = some (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2761 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1],[146],100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[318]? = some (⟨35,(2),[1],[146],100⟩) from rfl))
private theorem rec2762 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1],[151],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[319]? = some (⟨35,(2),[1],[151],101⟩) from rfl))
private theorem rec2763 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,2],[147],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[320]? = some (⟨35,(2),[1,2],[147],101⟩) from rfl))
private theorem rec2766 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,2,5,6],[150],139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[323]? = some (⟨35,(2),[1,2,5,6],[150],139⟩) from rfl))
private theorem rec2778 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1],[151],139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[335]? = some (⟨35,(3),[1],[151],139⟩) from rfl))
private theorem rec2779 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1],[147],185⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[336]? = some (⟨35,(3),[1],[147],185⟩) from rfl))
private theorem rec2781 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[338]? = some (⟨35,(3),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2788 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(4),[1],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[345]? = some (⟨35,(4),[1],[151],2⟩) from rfl))
private theorem rec2789 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(4),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[346]? = some (⟨35,(4),[1,2],[147,190],2⟩) from rfl))
private theorem rec2790 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[347]? = some (⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2793 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(5),[1],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[350]? = some (⟨35,(5),[1],[151],2⟩) from rfl))
private theorem rec2794 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(5),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[351]? = some (⟨35,(5),[1,2],[147,190],2⟩) from rfl))
private theorem rec2795 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[352]? = some (⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2798 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1],[151],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[355]? = some (⟨35,(6),[1],[151],101⟩) from rfl))
private theorem rec2799 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1],[146],102⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[356]? = some (⟨35,(6),[1],[146],102⟩) from rfl))
private theorem rec2800 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,2],[147],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[357]? = some (⟨35,(6),[1,2],[147],101⟩) from rfl))
private theorem rec2803 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,2,5,6],[150],140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[360]? = some (⟨35,(6),[1,2,5,6],[150],140⟩) from rfl))
private theorem rec2815 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1],[151],140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[372]? = some (⟨35,(7),[1],[151],140⟩) from rfl))
private theorem rec2816 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1],[147],186⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[373]? = some (⟨35,(7),[1],[147],186⟩) from rfl))
private theorem rec2818 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[375]? = some (⟨35,(7),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2825 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(8),[1],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[382]? = some (⟨35,(8),[1],[151],2⟩) from rfl))
private theorem rec2826 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(8),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[383]? = some (⟨35,(8),[1,2],[147,190],2⟩) from rfl))
private theorem rec2827 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[384]? = some (⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2830 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(9),[1],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[387]? = some (⟨35,(9),[1],[151],2⟩) from rfl))
private theorem rec2831 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(9),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[388]? = some (⟨35,(9),[1,2],[147,190],2⟩) from rfl))
private theorem rec2832 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[389]? = some (⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2835 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1],[151],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[392]? = some (⟨35,(10),[1],[151],101⟩) from rfl))
private theorem rec2836 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1],[146],103⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[393]? = some (⟨35,(10),[1],[146],103⟩) from rfl))
private theorem rec2837 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,2],[147],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[394]? = some (⟨35,(10),[1,2],[147],101⟩) from rfl))
private theorem rec2840 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,2,5,6],[150],141⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[397]? = some (⟨35,(10),[1,2,5,6],[150],141⟩) from rfl))
private theorem rec2852 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1],[151],144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[409]? = some (⟨35,(11),[1],[151],144⟩) from rfl))
private theorem rec2853 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1],[147],187⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[410]? = some (⟨35,(11),[1],[147],187⟩) from rfl))
private theorem rec2855 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[412]? = some (⟨35,(11),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2862 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(12),[1],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[419]? = some (⟨35,(12),[1],[151],2⟩) from rfl))
private theorem rec2863 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(12),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[420]? = some (⟨35,(12),[1,2],[147,190],2⟩) from rfl))
private theorem rec2864 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(12),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[421]? = some (⟨35,(12),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2867 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(13),[1],[151],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[424]? = some (⟨35,(13),[1],[151],2⟩) from rfl))
private theorem rec2868 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(13),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[425]? = some (⟨35,(13),[1,2],[147,190],2⟩) from rfl))
private theorem rec2869 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(13),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[426]? = some (⟨35,(13),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2872 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1],[151],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[429]? = some (⟨35,(14),[1],[151],101⟩) from rfl))
private theorem rec2873 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1],[146],104⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[430]? = some (⟨35,(14),[1],[146],104⟩) from rfl))
private theorem rec2874 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,2],[147],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[431]? = some (⟨35,(14),[1,2],[147],101⟩) from rfl))
private theorem rec2877 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,2,5,6],[150],142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[434]? = some (⟨35,(14),[1,2,5,6],[150],142⟩) from rfl))
private theorem rec2889 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1],[151],142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[446]? = some (⟨35,(15),[1],[151],142⟩) from rfl))
private theorem rec2890 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1],[147],188⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[447]? = some (⟨35,(15),[1],[147],188⟩) from rfl))
private theorem rec2892 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[449]? = some (⟨35,(15),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2900 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[457]? = some (⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩) from rfl))
private theorem rec2901 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,2,13,14],[147],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[458]? = some (⟨36,(5),[1,2,13,14],[147],105⟩) from rfl))
private theorem rec2905 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,13],[151],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[462]? = some (⟨36,(5),[1,13],[151],105⟩) from rfl))
private theorem rec2910 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,2,5,6,13,14],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[467]? = some (⟨36,(7),[1,2,5,6,13,14],[150],3⟩) from rfl))
private theorem rec2911 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,2,5,6,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[468]? = some (⟨36,(7),[1,2,5,6,14],[131,146],3⟩) from rfl))
private theorem rec2912 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,2,14],[147,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[469]? = some (⟨36,(7),[1,2,14],[147,190],3⟩) from rfl))
private theorem rec2915 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[472]? = some (⟨36,(7),[1,13],[151],3⟩) from rfl))
private theorem rec2921 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,2,5,6,13,14],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[478]? = some (⟨36,(8),[1,2,5,6,13,14],[150],3⟩) from rfl))
private theorem rec2925 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[482]? = some (⟨36,(8),[1,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2927 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[484]? = some (⟨36,(8),[1,13],[151],3⟩) from rfl))
private theorem rec2928 (si parent : ℕ) (hs : si ∈ ([1, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[485]? = some (⟨36,(8),[1,13,14],[147],3⟩) from rfl))
private theorem rec2935 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[1,2,5,6,13,14],[150],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[492]? = some (⟨36,(9),[1,2,5,6,13,14],[150],143⟩) from rfl))
private theorem rec2938 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([131, 146, 147] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[1,13],[131,146,147],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[495]? = some (⟨36,(9),[1,13],[131,146,147],105⟩) from rfl))
private theorem rec2939 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[1,13],[151],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[496]? = some (⟨36,(9),[1,13],[151],143⟩) from rfl))
private theorem rec2948 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[505]? = some (⟨36,(15),[1],[151],3⟩) from rfl))
private theorem rec2950 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1,2,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[507]? = some (⟨36,(15),[1,2,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2951 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1,2,5,6,14],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[508]? = some (⟨36,(15),[1,2,5,6,14],[150],3⟩) from rfl))
private theorem rec2952 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1,2,13,14],[147,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[509]? = some (⟨36,(15),[1,2,13,14],[147,190],3⟩) from rfl))
private theorem rec2958 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,2,5,6,13,14],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[515]? = some (⟨36,(16),[1,2,5,6,13,14],[150],3⟩) from rfl))
private theorem rec2962 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[519]? = some (⟨36,(16),[1,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2964 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,13],[151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[521]? = some (⟨36,(16),[1,13],[151],3⟩) from rfl))
private theorem rec2965 (si parent : ℕ) (hs : si ∈ ([1, 13, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,13,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[522]? = some (⟨36,(16),[1,13,14],[147],3⟩) from rfl))
private theorem rec2970 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([134, 135, 151] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[1],[134,135,151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[527]? = some (⟨36,(17),[1],[134,135,151],3⟩) from rfl))
private theorem rec2972 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[1,2,6,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[529]? = some (⟨36,(17),[1,2,6,14],[131,146,150],3⟩) from rfl))
private theorem rec2974 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[1,2,14],[147],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[531]? = some (⟨36,(17),[1,2,14],[147],3⟩) from rfl))
private theorem rec2981 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([134, 135, 151] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[1],[134,135,151],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[538]? = some (⟨36,(19),[1],[134,135,151],3⟩) from rfl))
private theorem rec2982 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 147, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[1,2],[130,131,146,147,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[539]? = some (⟨36,(19),[1,2],[130,131,146,147,150],3⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0001_coverage0001_parents_0144_0160 : ∀ pl ∈ ((section14State section14Catalog 1).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 144).take 16, section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 1).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 144).take 16 = [⟨1,144,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,145,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,146,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,147,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,148,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,149,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,150,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,151,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,152,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,153,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,154,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,155,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,156,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,157,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,158,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,159,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec361 1 144 (by decide) (by decide)
  · left
    exact rec361 1 145 (by decide) (by decide)
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
        exact rec499 1 146 (by decide) (by decide)
      · right
        exact rec516 1 146 (by decide) (by decide)
      · right
        exact rec533 1 146 (by decide) (by decide)
      · right
        exact rec550 1 146 (by decide) (by decide)
      · right
        exact rec567 1 146 (by decide) (by decide)
      · right
        exact rec584 1 146 (by decide) (by decide)
      · right
        exact rec601 1 146 (by decide) (by decide)
      · right
        exact rec618 1 146 (by decide) (by decide)
      · right
        exact rec635 1 146 (by decide) (by decide)
      · right
        exact rec652 1 146 (by decide) (by decide)
      · right
        exact rec669 1 146 (by decide) (by decide)
      · right
        exact rec686 1 146 (by decide) (by decide)
      · right
        exact rec703 1 146 (by decide) (by decide)
      · right
        exact rec720 1 146 (by decide) (by decide)
      · right
        exact rec737 1 146 (by decide) (by decide)
      · right
        exact rec754 1 146 (by decide) (by decide)
      · right
        exact rec771 1 146 (by decide) (by decide)
      · right
        exact rec788 1 146 (by decide) (by decide)
      · right
        exact rec805 1 146 (by decide) (by decide)
      · right
        exact rec822 1 146 (by decide) (by decide)
      · right
        exact rec839 1 146 (by decide) (by decide)
      · right
        exact rec856 1 146 (by decide) (by decide)
      · right
        exact rec873 1 146 (by decide) (by decide)
      · right
        exact rec890 1 146 (by decide) (by decide)
      · right
        exact rec907 1 146 (by decide) (by decide)
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
        exact rec919 1 146 (by decide) (by decide)
      · right
        exact rec930 1 146 (by decide) (by decide)
      · right
        exact rec941 1 146 (by decide) (by decide)
      · right
        exact rec952 1 146 (by decide) (by decide)
      · right
        exact rec963 1 146 (by decide) (by decide)
      · right
        exact rec974 1 146 (by decide) (by decide)
      · right
        exact rec985 1 146 (by decide) (by decide)
      · right
        exact rec996 1 146 (by decide) (by decide)
      · right
        exact rec1007 1 146 (by decide) (by decide)
      · right
        exact rec1018 1 146 (by decide) (by decide)
      · right
        exact rec1029 1 146 (by decide) (by decide)
      · right
        exact rec1040 1 146 (by decide) (by decide)
      · right
        exact rec1051 1 146 (by decide) (by decide)
      · right
        exact rec1062 1 146 (by decide) (by decide)
      · right
        exact rec1073 1 146 (by decide) (by decide)
      · right
        exact rec1084 1 146 (by decide) (by decide)
      · right
        exact rec1095 1 146 (by decide) (by decide)
      · right
        exact rec1106 1 146 (by decide) (by decide)
      · right
        exact rec1117 1 146 (by decide) (by decide)
      · right
        exact rec1128 1 146 (by decide) (by decide)
      · right
        exact rec1139 1 146 (by decide) (by decide)
      · right
        exact rec1150 1 146 (by decide) (by decide)
      · right
        exact rec1161 1 146 (by decide) (by decide)
      · right
        exact rec1172 1 146 (by decide) (by decide)
      · right
        exact rec1183 1 146 (by decide) (by decide)
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
        exact rec1194 1 146 (by decide) (by decide)
      · right
        exact rec1201 1 146 (by decide) (by decide)
      · right
        exact rec1208 1 146 (by decide) (by decide)
      · right
        exact rec1215 1 146 (by decide) (by decide)
      · right
        exact rec1222 1 146 (by decide) (by decide)
      · right
        exact rec1229 1 146 (by decide) (by decide)
      · right
        exact rec1236 1 146 (by decide) (by decide)
      · right
        exact rec1243 1 146 (by decide) (by decide)
      · right
        exact rec1250 1 146 (by decide) (by decide)
      · right
        exact rec1257 1 146 (by decide) (by decide)
      · right
        exact rec1264 1 146 (by decide) (by decide)
      · right
        exact rec1271 1 146 (by decide) (by decide)
      · right
        exact rec1278 1 146 (by decide) (by decide)
      · right
        exact rec1285 1 146 (by decide) (by decide)
      · right
        exact rec1292 1 146 (by decide) (by decide)
      · right
        exact rec1299 1 146 (by decide) (by decide)
      · right
        exact rec1306 1 146 (by decide) (by decide)
      · right
        exact rec1313 1 146 (by decide) (by decide)
      · right
        exact rec1320 1 146 (by decide) (by decide)
      · right
        exact rec1327 1 146 (by decide) (by decide)
      · right
        exact rec1334 1 146 (by decide) (by decide)
      · right
        exact rec1341 1 146 (by decide) (by decide)
      · right
        exact rec1348 1 146 (by decide) (by decide)
      · right
        exact rec1355 1 146 (by decide) (by decide)
      · right
        exact rec1362 1 146 (by decide) (by decide)
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
        exact rec1369 1 146 (by decide) (by decide)
      · right
        exact rec1390 1 146 (by decide) (by decide)
      · right
        exact rec1414 1 146 (by decide) (by decide)
      · right
        exact rec1438 1 146 (by decide) (by decide)
      · right
        exact rec1462 1 146 (by decide) (by decide)
      · right
        exact rec1486 1 146 (by decide) (by decide)
      · right
        exact rec1507 1 146 (by decide) (by decide)
      · right
        exact rec1531 1 146 (by decide) (by decide)
      · right
        exact rec1555 1 146 (by decide) (by decide)
      · right
        exact rec1579 1 146 (by decide) (by decide)
      · right
        exact rec1603 1 146 (by decide) (by decide)
      · right
        exact rec1624 1 146 (by decide) (by decide)
      · right
        exact rec1648 1 146 (by decide) (by decide)
      · right
        exact rec1672 1 146 (by decide) (by decide)
      · right
        exact rec1696 1 146 (by decide) (by decide)
      · right
        exact rec1720 1 146 (by decide) (by decide)
      · right
        exact rec1741 1 146 (by decide) (by decide)
      · right
        exact rec1765 1 146 (by decide) (by decide)
      · right
        exact rec1789 1 146 (by decide) (by decide)
      · right
        exact rec1813 1 146 (by decide) (by decide)
      · right
        exact rec1837 1 146 (by decide) (by decide)
      · right
        exact rec1858 1 146 (by decide) (by decide)
      · right
        exact rec1882 1 146 (by decide) (by decide)
      · right
        exact rec1906 1 146 (by decide) (by decide)
      · right
        exact rec1930 1 146 (by decide) (by decide)
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
        exact rec1953 1 146 (by decide) (by decide)
      · right
        exact rec1969 1 146 (by decide) (by decide)
      · right
        exact rec1985 1 146 (by decide) (by decide)
      · right
        exact rec2001 1 146 (by decide) (by decide)
      · right
        exact rec2017 1 146 (by decide) (by decide)
      · right
        exact rec2033 1 146 (by decide) (by decide)
      · right
        exact rec2049 1 146 (by decide) (by decide)
      · right
        exact rec2065 1 146 (by decide) (by decide)
      · right
        exact rec2081 1 146 (by decide) (by decide)
      · right
        exact rec2097 1 146 (by decide) (by decide)
      · right
        exact rec2113 1 146 (by decide) (by decide)
      · right
        exact rec2129 1 146 (by decide) (by decide)
      · right
        exact rec2145 1 146 (by decide) (by decide)
      · right
        exact rec2161 1 146 (by decide) (by decide)
      · right
        exact rec2177 1 146 (by decide) (by decide)
      · right
        exact rec2193 1 146 (by decide) (by decide)
      · right
        exact rec2209 1 146 (by decide) (by decide)
      · right
        exact rec2225 1 146 (by decide) (by decide)
      · right
        exact rec2241 1 146 (by decide) (by decide)
      · right
        exact rec2257 1 146 (by decide) (by decide)
      · right
        exact rec2273 1 146 (by decide) (by decide)
      · right
        exact rec2289 1 146 (by decide) (by decide)
      · right
        exact rec2305 1 146 (by decide) (by decide)
      · right
        exact rec2321 1 146 (by decide) (by decide)
      · right
        exact rec2337 1 146 (by decide) (by decide)
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
        exact rec2358 1 146 (by decide) (by decide)
      · right
        exact rec2374 1 146 (by decide) (by decide)
      · right
        exact rec2388 1 146 (by decide) (by decide)
      · right
        exact rec2411 1 146 (by decide) (by decide)
      · right
        exact rec2435 1 146 (by decide) (by decide)
      · right
        exact rec2459 1 146 (by decide) (by decide)
      · right
        exact rec2483 1 146 (by decide) (by decide)
      · right
        exact rec2507 1 146 (by decide) (by decide)
      · right
        exact rec2531 1 146 (by decide) (by decide)
      · right
        exact rec2555 1 146 (by decide) (by decide)
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
        exact rec2576 1 146 (by decide) (by decide)
      · right
        exact rec2586 1 146 (by decide) (by decide)
      · right
        exact rec2598 1 146 (by decide) (by decide)
      · right
        exact rec2612 1 146 (by decide) (by decide)
      · right
        exact rec2624 1 146 (by decide) (by decide)
      · right
        exact rec2633 1 146 (by decide) (by decide)
      · right
        exact rec2648 1 146 (by decide) (by decide)
      · right
        exact rec2659 1 146 (by decide) (by decide)
      · right
        exact rec2668 1 146 (by decide) (by decide)
      · right
        exact rec2678 1 146 (by decide) (by decide)
      · right
        exact rec2688 1 146 (by decide) (by decide)
      · right
        exact rec2698 1 146 (by decide) (by decide)
      · right
        exact rec2707 1 146 (by decide) (by decide)
      · right
        exact rec2719 1 146 (by decide) (by decide)
      · right
        exact rec2732 1 146 (by decide) (by decide)
      · right
        exact rec2743 1 146 (by decide) (by decide)
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
        exact rec2753 1 146 (by decide) (by decide)
      · right
        exact rec2758 1 146 (by decide) (by decide)
      · right
        exact rec2761 1 146 (by decide) (by decide)
      · right
        exact rec2781 1 146 (by decide) (by decide)
      · right
        exact rec2790 1 146 (by decide) (by decide)
      · right
        exact rec2795 1 146 (by decide) (by decide)
      · right
        exact rec2799 1 146 (by decide) (by decide)
      · right
        exact rec2818 1 146 (by decide) (by decide)
      · right
        exact rec2827 1 146 (by decide) (by decide)
      · right
        exact rec2832 1 146 (by decide) (by decide)
      · right
        exact rec2836 1 146 (by decide) (by decide)
      · right
        exact rec2855 1 146 (by decide) (by decide)
      · right
        exact rec2864 1 146 (by decide) (by decide)
      · right
        exact rec2869 1 146 (by decide) (by decide)
      · right
        exact rec2873 1 146 (by decide) (by decide)
      · right
        exact rec2892 1 146 (by decide) (by decide)
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
        exact rec2900 1 146 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2911 1 146 (by decide) (by decide)
      · right
        exact rec2925 1 146 (by decide) (by decide)
      · right
        exact rec2938 1 146 (by decide) (by decide)
      · left
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
        exact rec2950 1 146 (by decide) (by decide)
      · right
        exact rec2962 1 146 (by decide) (by decide)
      · right
        exact rec2972 1 146 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2982 1 146 (by decide) (by decide)
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
        exact rec501 1 147 (by decide) (by decide)
      · right
        exact rec518 1 147 (by decide) (by decide)
      · right
        exact rec535 1 147 (by decide) (by decide)
      · right
        exact rec552 1 147 (by decide) (by decide)
      · right
        exact rec569 1 147 (by decide) (by decide)
      · right
        exact rec586 1 147 (by decide) (by decide)
      · right
        exact rec603 1 147 (by decide) (by decide)
      · right
        exact rec620 1 147 (by decide) (by decide)
      · right
        exact rec637 1 147 (by decide) (by decide)
      · right
        exact rec654 1 147 (by decide) (by decide)
      · right
        exact rec671 1 147 (by decide) (by decide)
      · right
        exact rec688 1 147 (by decide) (by decide)
      · right
        exact rec705 1 147 (by decide) (by decide)
      · right
        exact rec722 1 147 (by decide) (by decide)
      · right
        exact rec739 1 147 (by decide) (by decide)
      · right
        exact rec756 1 147 (by decide) (by decide)
      · right
        exact rec773 1 147 (by decide) (by decide)
      · right
        exact rec790 1 147 (by decide) (by decide)
      · right
        exact rec807 1 147 (by decide) (by decide)
      · right
        exact rec824 1 147 (by decide) (by decide)
      · right
        exact rec841 1 147 (by decide) (by decide)
      · right
        exact rec858 1 147 (by decide) (by decide)
      · right
        exact rec875 1 147 (by decide) (by decide)
      · right
        exact rec892 1 147 (by decide) (by decide)
      · right
        exact rec909 1 147 (by decide) (by decide)
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
        exact rec920 1 147 (by decide) (by decide)
      · right
        exact rec931 1 147 (by decide) (by decide)
      · right
        exact rec942 1 147 (by decide) (by decide)
      · right
        exact rec953 1 147 (by decide) (by decide)
      · right
        exact rec964 1 147 (by decide) (by decide)
      · right
        exact rec975 1 147 (by decide) (by decide)
      · right
        exact rec986 1 147 (by decide) (by decide)
      · right
        exact rec997 1 147 (by decide) (by decide)
      · right
        exact rec1008 1 147 (by decide) (by decide)
      · right
        exact rec1019 1 147 (by decide) (by decide)
      · right
        exact rec1030 1 147 (by decide) (by decide)
      · right
        exact rec1041 1 147 (by decide) (by decide)
      · right
        exact rec1052 1 147 (by decide) (by decide)
      · right
        exact rec1063 1 147 (by decide) (by decide)
      · right
        exact rec1074 1 147 (by decide) (by decide)
      · right
        exact rec1085 1 147 (by decide) (by decide)
      · right
        exact rec1096 1 147 (by decide) (by decide)
      · right
        exact rec1107 1 147 (by decide) (by decide)
      · right
        exact rec1118 1 147 (by decide) (by decide)
      · right
        exact rec1129 1 147 (by decide) (by decide)
      · right
        exact rec1140 1 147 (by decide) (by decide)
      · right
        exact rec1151 1 147 (by decide) (by decide)
      · right
        exact rec1162 1 147 (by decide) (by decide)
      · right
        exact rec1173 1 147 (by decide) (by decide)
      · right
        exact rec1184 1 147 (by decide) (by decide)
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
        exact rec1195 1 147 (by decide) (by decide)
      · right
        exact rec1202 1 147 (by decide) (by decide)
      · right
        exact rec1209 1 147 (by decide) (by decide)
      · right
        exact rec1216 1 147 (by decide) (by decide)
      · right
        exact rec1223 1 147 (by decide) (by decide)
      · right
        exact rec1230 1 147 (by decide) (by decide)
      · right
        exact rec1237 1 147 (by decide) (by decide)
      · right
        exact rec1244 1 147 (by decide) (by decide)
      · right
        exact rec1251 1 147 (by decide) (by decide)
      · right
        exact rec1258 1 147 (by decide) (by decide)
      · right
        exact rec1265 1 147 (by decide) (by decide)
      · right
        exact rec1272 1 147 (by decide) (by decide)
      · right
        exact rec1279 1 147 (by decide) (by decide)
      · right
        exact rec1286 1 147 (by decide) (by decide)
      · right
        exact rec1293 1 147 (by decide) (by decide)
      · right
        exact rec1300 1 147 (by decide) (by decide)
      · right
        exact rec1307 1 147 (by decide) (by decide)
      · right
        exact rec1314 1 147 (by decide) (by decide)
      · right
        exact rec1321 1 147 (by decide) (by decide)
      · right
        exact rec1328 1 147 (by decide) (by decide)
      · right
        exact rec1335 1 147 (by decide) (by decide)
      · right
        exact rec1342 1 147 (by decide) (by decide)
      · right
        exact rec1349 1 147 (by decide) (by decide)
      · right
        exact rec1356 1 147 (by decide) (by decide)
      · right
        exact rec1363 1 147 (by decide) (by decide)
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
        exact rec1372 1 147 (by decide) (by decide)
      · right
        exact rec1392 1 147 (by decide) (by decide)
      · right
        exact rec1416 1 147 (by decide) (by decide)
      · right
        exact rec1440 1 147 (by decide) (by decide)
      · right
        exact rec1464 1 147 (by decide) (by decide)
      · right
        exact rec1489 1 147 (by decide) (by decide)
      · right
        exact rec1509 1 147 (by decide) (by decide)
      · right
        exact rec1533 1 147 (by decide) (by decide)
      · right
        exact rec1557 1 147 (by decide) (by decide)
      · right
        exact rec1581 1 147 (by decide) (by decide)
      · right
        exact rec1606 1 147 (by decide) (by decide)
      · right
        exact rec1626 1 147 (by decide) (by decide)
      · right
        exact rec1650 1 147 (by decide) (by decide)
      · right
        exact rec1674 1 147 (by decide) (by decide)
      · right
        exact rec1698 1 147 (by decide) (by decide)
      · right
        exact rec1723 1 147 (by decide) (by decide)
      · right
        exact rec1743 1 147 (by decide) (by decide)
      · right
        exact rec1767 1 147 (by decide) (by decide)
      · right
        exact rec1791 1 147 (by decide) (by decide)
      · right
        exact rec1815 1 147 (by decide) (by decide)
      · right
        exact rec1840 1 147 (by decide) (by decide)
      · right
        exact rec1860 1 147 (by decide) (by decide)
      · right
        exact rec1884 1 147 (by decide) (by decide)
      · right
        exact rec1908 1 147 (by decide) (by decide)
      · right
        exact rec1932 1 147 (by decide) (by decide)
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
        exact rec1955 1 147 (by decide) (by decide)
      · right
        exact rec1971 1 147 (by decide) (by decide)
      · right
        exact rec1987 1 147 (by decide) (by decide)
      · right
        exact rec2003 1 147 (by decide) (by decide)
      · right
        exact rec2019 1 147 (by decide) (by decide)
      · right
        exact rec2035 1 147 (by decide) (by decide)
      · right
        exact rec2051 1 147 (by decide) (by decide)
      · right
        exact rec2067 1 147 (by decide) (by decide)
      · right
        exact rec2083 1 147 (by decide) (by decide)
      · right
        exact rec2099 1 147 (by decide) (by decide)
      · right
        exact rec2115 1 147 (by decide) (by decide)
      · right
        exact rec2131 1 147 (by decide) (by decide)
      · right
        exact rec2147 1 147 (by decide) (by decide)
      · right
        exact rec2163 1 147 (by decide) (by decide)
      · right
        exact rec2179 1 147 (by decide) (by decide)
      · right
        exact rec2195 1 147 (by decide) (by decide)
      · right
        exact rec2211 1 147 (by decide) (by decide)
      · right
        exact rec2227 1 147 (by decide) (by decide)
      · right
        exact rec2243 1 147 (by decide) (by decide)
      · right
        exact rec2259 1 147 (by decide) (by decide)
      · right
        exact rec2275 1 147 (by decide) (by decide)
      · right
        exact rec2291 1 147 (by decide) (by decide)
      · right
        exact rec2307 1 147 (by decide) (by decide)
      · right
        exact rec2323 1 147 (by decide) (by decide)
      · right
        exact rec2339 1 147 (by decide) (by decide)
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
        exact rec2356 1 147 (by decide) (by decide)
      · right
        exact rec2373 1 147 (by decide) (by decide)
      · right
        exact rec2385 1 147 (by decide) (by decide)
      · right
        exact rec2407 1 147 (by decide) (by decide)
      · right
        exact rec2431 1 147 (by decide) (by decide)
      · right
        exact rec2455 1 147 (by decide) (by decide)
      · right
        exact rec2479 1 147 (by decide) (by decide)
      · right
        exact rec2503 1 147 (by decide) (by decide)
      · right
        exact rec2527 1 147 (by decide) (by decide)
      · right
        exact rec2551 1 147 (by decide) (by decide)
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
        exact rec2572 1 147 (by decide) (by decide)
      · right
        exact rec2586 1 147 (by decide) (by decide)
      · right
        exact rec2600 1 147 (by decide) (by decide)
      · right
        exact rec2615 1 147 (by decide) (by decide)
      · right
        exact rec2620 1 147 (by decide) (by decide)
      · right
        exact rec2634 1 147 (by decide) (by decide)
      · right
        exact rec2651 1 147 (by decide) (by decide)
      · right
        exact rec2662 1 147 (by decide) (by decide)
      · right
        exact rec2670 1 147 (by decide) (by decide)
      · right
        exact rec2680 1 147 (by decide) (by decide)
      · right
        exact rec2689 1 147 (by decide) (by decide)
      · right
        exact rec2699 1 147 (by decide) (by decide)
      · right
        exact rec2706 1 147 (by decide) (by decide)
      · right
        exact rec2720 1 147 (by decide) (by decide)
      · right
        exact rec2734 1 147 (by decide) (by decide)
      · right
        exact rec2745 1 147 (by decide) (by decide)
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
        exact rec2752 1 147 (by decide) (by decide)
      · right
        exact rec2757 1 147 (by decide) (by decide)
      · right
        exact rec2763 1 147 (by decide) (by decide)
      · right
        exact rec2779 1 147 (by decide) (by decide)
      · right
        exact rec2789 1 147 (by decide) (by decide)
      · right
        exact rec2794 1 147 (by decide) (by decide)
      · right
        exact rec2800 1 147 (by decide) (by decide)
      · right
        exact rec2816 1 147 (by decide) (by decide)
      · right
        exact rec2826 1 147 (by decide) (by decide)
      · right
        exact rec2831 1 147 (by decide) (by decide)
      · right
        exact rec2837 1 147 (by decide) (by decide)
      · right
        exact rec2853 1 147 (by decide) (by decide)
      · right
        exact rec2863 1 147 (by decide) (by decide)
      · right
        exact rec2868 1 147 (by decide) (by decide)
      · right
        exact rec2874 1 147 (by decide) (by decide)
      · right
        exact rec2890 1 147 (by decide) (by decide)
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
        exact rec2901 1 147 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2912 1 147 (by decide) (by decide)
      · right
        exact rec2928 1 147 (by decide) (by decide)
      · right
        exact rec2938 1 147 (by decide) (by decide)
      · left
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
        exact rec2952 1 147 (by decide) (by decide)
      · right
        exact rec2965 1 147 (by decide) (by decide)
      · right
        exact rec2974 1 147 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2982 1 147 (by decide) (by decide)
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
    exact rec361 1 148 (by decide) (by decide)
  · left
    exact rec361 1 149 (by decide) (by decide)
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
        exact rec494 1 150 (by decide) (by decide)
      · right
        exact rec511 1 150 (by decide) (by decide)
      · right
        exact rec528 1 150 (by decide) (by decide)
      · right
        exact rec545 1 150 (by decide) (by decide)
      · right
        exact rec562 1 150 (by decide) (by decide)
      · right
        exact rec579 1 150 (by decide) (by decide)
      · right
        exact rec596 1 150 (by decide) (by decide)
      · right
        exact rec613 1 150 (by decide) (by decide)
      · right
        exact rec630 1 150 (by decide) (by decide)
      · right
        exact rec647 1 150 (by decide) (by decide)
      · right
        exact rec664 1 150 (by decide) (by decide)
      · right
        exact rec681 1 150 (by decide) (by decide)
      · right
        exact rec698 1 150 (by decide) (by decide)
      · right
        exact rec715 1 150 (by decide) (by decide)
      · right
        exact rec732 1 150 (by decide) (by decide)
      · right
        exact rec749 1 150 (by decide) (by decide)
      · right
        exact rec766 1 150 (by decide) (by decide)
      · right
        exact rec783 1 150 (by decide) (by decide)
      · right
        exact rec800 1 150 (by decide) (by decide)
      · right
        exact rec817 1 150 (by decide) (by decide)
      · right
        exact rec834 1 150 (by decide) (by decide)
      · right
        exact rec851 1 150 (by decide) (by decide)
      · right
        exact rec868 1 150 (by decide) (by decide)
      · right
        exact rec885 1 150 (by decide) (by decide)
      · right
        exact rec902 1 150 (by decide) (by decide)
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
        exact rec919 1 150 (by decide) (by decide)
      · right
        exact rec930 1 150 (by decide) (by decide)
      · right
        exact rec941 1 150 (by decide) (by decide)
      · right
        exact rec952 1 150 (by decide) (by decide)
      · right
        exact rec963 1 150 (by decide) (by decide)
      · right
        exact rec974 1 150 (by decide) (by decide)
      · right
        exact rec985 1 150 (by decide) (by decide)
      · right
        exact rec996 1 150 (by decide) (by decide)
      · right
        exact rec1007 1 150 (by decide) (by decide)
      · right
        exact rec1018 1 150 (by decide) (by decide)
      · right
        exact rec1029 1 150 (by decide) (by decide)
      · right
        exact rec1040 1 150 (by decide) (by decide)
      · right
        exact rec1051 1 150 (by decide) (by decide)
      · right
        exact rec1062 1 150 (by decide) (by decide)
      · right
        exact rec1073 1 150 (by decide) (by decide)
      · right
        exact rec1084 1 150 (by decide) (by decide)
      · right
        exact rec1095 1 150 (by decide) (by decide)
      · right
        exact rec1106 1 150 (by decide) (by decide)
      · right
        exact rec1117 1 150 (by decide) (by decide)
      · right
        exact rec1128 1 150 (by decide) (by decide)
      · right
        exact rec1139 1 150 (by decide) (by decide)
      · right
        exact rec1150 1 150 (by decide) (by decide)
      · right
        exact rec1161 1 150 (by decide) (by decide)
      · right
        exact rec1172 1 150 (by decide) (by decide)
      · right
        exact rec1183 1 150 (by decide) (by decide)
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
        exact rec1194 1 150 (by decide) (by decide)
      · right
        exact rec1201 1 150 (by decide) (by decide)
      · right
        exact rec1208 1 150 (by decide) (by decide)
      · right
        exact rec1215 1 150 (by decide) (by decide)
      · right
        exact rec1222 1 150 (by decide) (by decide)
      · right
        exact rec1229 1 150 (by decide) (by decide)
      · right
        exact rec1236 1 150 (by decide) (by decide)
      · right
        exact rec1243 1 150 (by decide) (by decide)
      · right
        exact rec1250 1 150 (by decide) (by decide)
      · right
        exact rec1257 1 150 (by decide) (by decide)
      · right
        exact rec1264 1 150 (by decide) (by decide)
      · right
        exact rec1271 1 150 (by decide) (by decide)
      · right
        exact rec1278 1 150 (by decide) (by decide)
      · right
        exact rec1285 1 150 (by decide) (by decide)
      · right
        exact rec1292 1 150 (by decide) (by decide)
      · right
        exact rec1299 1 150 (by decide) (by decide)
      · right
        exact rec1306 1 150 (by decide) (by decide)
      · right
        exact rec1313 1 150 (by decide) (by decide)
      · right
        exact rec1320 1 150 (by decide) (by decide)
      · right
        exact rec1327 1 150 (by decide) (by decide)
      · right
        exact rec1334 1 150 (by decide) (by decide)
      · right
        exact rec1341 1 150 (by decide) (by decide)
      · right
        exact rec1348 1 150 (by decide) (by decide)
      · right
        exact rec1355 1 150 (by decide) (by decide)
      · right
        exact rec1362 1 150 (by decide) (by decide)
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
        exact rec1370 1 150 (by decide) (by decide)
      · right
        exact rec1393 1 150 (by decide) (by decide)
      · right
        exact rec1417 1 150 (by decide) (by decide)
      · right
        exact rec1441 1 150 (by decide) (by decide)
      · right
        exact rec1465 1 150 (by decide) (by decide)
      · right
        exact rec1487 1 150 (by decide) (by decide)
      · right
        exact rec1510 1 150 (by decide) (by decide)
      · right
        exact rec1534 1 150 (by decide) (by decide)
      · right
        exact rec1558 1 150 (by decide) (by decide)
      · right
        exact rec1582 1 150 (by decide) (by decide)
      · right
        exact rec1604 1 150 (by decide) (by decide)
      · right
        exact rec1627 1 150 (by decide) (by decide)
      · right
        exact rec1651 1 150 (by decide) (by decide)
      · right
        exact rec1675 1 150 (by decide) (by decide)
      · right
        exact rec1699 1 150 (by decide) (by decide)
      · right
        exact rec1721 1 150 (by decide) (by decide)
      · right
        exact rec1744 1 150 (by decide) (by decide)
      · right
        exact rec1768 1 150 (by decide) (by decide)
      · right
        exact rec1792 1 150 (by decide) (by decide)
      · right
        exact rec1816 1 150 (by decide) (by decide)
      · right
        exact rec1838 1 150 (by decide) (by decide)
      · right
        exact rec1861 1 150 (by decide) (by decide)
      · right
        exact rec1885 1 150 (by decide) (by decide)
      · right
        exact rec1909 1 150 (by decide) (by decide)
      · right
        exact rec1933 1 150 (by decide) (by decide)
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
        exact rec1958 1 150 (by decide) (by decide)
      · right
        exact rec1974 1 150 (by decide) (by decide)
      · right
        exact rec1990 1 150 (by decide) (by decide)
      · right
        exact rec2006 1 150 (by decide) (by decide)
      · right
        exact rec2022 1 150 (by decide) (by decide)
      · right
        exact rec2038 1 150 (by decide) (by decide)
      · right
        exact rec2054 1 150 (by decide) (by decide)
      · right
        exact rec2070 1 150 (by decide) (by decide)
      · right
        exact rec2086 1 150 (by decide) (by decide)
      · right
        exact rec2102 1 150 (by decide) (by decide)
      · right
        exact rec2118 1 150 (by decide) (by decide)
      · right
        exact rec2134 1 150 (by decide) (by decide)
      · right
        exact rec2150 1 150 (by decide) (by decide)
      · right
        exact rec2166 1 150 (by decide) (by decide)
      · right
        exact rec2182 1 150 (by decide) (by decide)
      · right
        exact rec2198 1 150 (by decide) (by decide)
      · right
        exact rec2214 1 150 (by decide) (by decide)
      · right
        exact rec2230 1 150 (by decide) (by decide)
      · right
        exact rec2246 1 150 (by decide) (by decide)
      · right
        exact rec2262 1 150 (by decide) (by decide)
      · right
        exact rec2278 1 150 (by decide) (by decide)
      · right
        exact rec2294 1 150 (by decide) (by decide)
      · right
        exact rec2310 1 150 (by decide) (by decide)
      · right
        exact rec2326 1 150 (by decide) (by decide)
      · right
        exact rec2342 1 150 (by decide) (by decide)
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
        exact rec2358 1 150 (by decide) (by decide)
      · right
        exact rec2374 1 150 (by decide) (by decide)
      · right
        exact rec2389 1 150 (by decide) (by decide)
      · right
        exact rec2408 1 150 (by decide) (by decide)
      · right
        exact rec2432 1 150 (by decide) (by decide)
      · right
        exact rec2456 1 150 (by decide) (by decide)
      · right
        exact rec2480 1 150 (by decide) (by decide)
      · right
        exact rec2504 1 150 (by decide) (by decide)
      · right
        exact rec2528 1 150 (by decide) (by decide)
      · right
        exact rec2552 1 150 (by decide) (by decide)
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
        exact rec2576 1 150 (by decide) (by decide)
      · right
        exact rec2586 1 150 (by decide) (by decide)
      · right
        exact rec2598 1 150 (by decide) (by decide)
      · right
        exact rec2612 1 150 (by decide) (by decide)
      · right
        exact rec2624 1 150 (by decide) (by decide)
      · right
        exact rec2633 1 150 (by decide) (by decide)
      · right
        exact rec2648 1 150 (by decide) (by decide)
      · right
        exact rec2659 1 150 (by decide) (by decide)
      · right
        exact rec2668 1 150 (by decide) (by decide)
      · right
        exact rec2678 1 150 (by decide) (by decide)
      · right
        exact rec2688 1 150 (by decide) (by decide)
      · right
        exact rec2698 1 150 (by decide) (by decide)
      · right
        exact rec2707 1 150 (by decide) (by decide)
      · right
        exact rec2719 1 150 (by decide) (by decide)
      · right
        exact rec2732 1 150 (by decide) (by decide)
      · right
        exact rec2743 1 150 (by decide) (by decide)
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
        exact rec2753 1 150 (by decide) (by decide)
      · right
        exact rec2758 1 150 (by decide) (by decide)
      · right
        exact rec2766 1 150 (by decide) (by decide)
      · right
        exact rec2781 1 150 (by decide) (by decide)
      · right
        exact rec2790 1 150 (by decide) (by decide)
      · right
        exact rec2795 1 150 (by decide) (by decide)
      · right
        exact rec2803 1 150 (by decide) (by decide)
      · right
        exact rec2818 1 150 (by decide) (by decide)
      · right
        exact rec2827 1 150 (by decide) (by decide)
      · right
        exact rec2832 1 150 (by decide) (by decide)
      · right
        exact rec2840 1 150 (by decide) (by decide)
      · right
        exact rec2855 1 150 (by decide) (by decide)
      · right
        exact rec2864 1 150 (by decide) (by decide)
      · right
        exact rec2869 1 150 (by decide) (by decide)
      · right
        exact rec2877 1 150 (by decide) (by decide)
      · right
        exact rec2892 1 150 (by decide) (by decide)
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
        exact rec2900 1 150 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2910 1 150 (by decide) (by decide)
      · right
        exact rec2921 1 150 (by decide) (by decide)
      · right
        exact rec2935 1 150 (by decide) (by decide)
      · left
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
        exact rec2951 1 150 (by decide) (by decide)
      · right
        exact rec2958 1 150 (by decide) (by decide)
      · right
        exact rec2972 1 150 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2982 1 150 (by decide) (by decide)
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
        exact rec500 1 151 (by decide) (by decide)
      · right
        exact rec517 1 151 (by decide) (by decide)
      · right
        exact rec534 1 151 (by decide) (by decide)
      · right
        exact rec551 1 151 (by decide) (by decide)
      · right
        exact rec568 1 151 (by decide) (by decide)
      · right
        exact rec585 1 151 (by decide) (by decide)
      · right
        exact rec602 1 151 (by decide) (by decide)
      · right
        exact rec619 1 151 (by decide) (by decide)
      · right
        exact rec636 1 151 (by decide) (by decide)
      · right
        exact rec653 1 151 (by decide) (by decide)
      · right
        exact rec670 1 151 (by decide) (by decide)
      · right
        exact rec687 1 151 (by decide) (by decide)
      · right
        exact rec704 1 151 (by decide) (by decide)
      · right
        exact rec721 1 151 (by decide) (by decide)
      · right
        exact rec738 1 151 (by decide) (by decide)
      · right
        exact rec755 1 151 (by decide) (by decide)
      · right
        exact rec772 1 151 (by decide) (by decide)
      · right
        exact rec789 1 151 (by decide) (by decide)
      · right
        exact rec806 1 151 (by decide) (by decide)
      · right
        exact rec823 1 151 (by decide) (by decide)
      · right
        exact rec840 1 151 (by decide) (by decide)
      · right
        exact rec857 1 151 (by decide) (by decide)
      · right
        exact rec874 1 151 (by decide) (by decide)
      · right
        exact rec891 1 151 (by decide) (by decide)
      · right
        exact rec908 1 151 (by decide) (by decide)
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
        exact rec924 1 151 (by decide) (by decide)
      · right
        exact rec935 1 151 (by decide) (by decide)
      · right
        exact rec946 1 151 (by decide) (by decide)
      · right
        exact rec957 1 151 (by decide) (by decide)
      · right
        exact rec968 1 151 (by decide) (by decide)
      · right
        exact rec979 1 151 (by decide) (by decide)
      · right
        exact rec990 1 151 (by decide) (by decide)
      · right
        exact rec1001 1 151 (by decide) (by decide)
      · right
        exact rec1012 1 151 (by decide) (by decide)
      · right
        exact rec1023 1 151 (by decide) (by decide)
      · right
        exact rec1034 1 151 (by decide) (by decide)
      · right
        exact rec1045 1 151 (by decide) (by decide)
      · right
        exact rec1056 1 151 (by decide) (by decide)
      · right
        exact rec1067 1 151 (by decide) (by decide)
      · right
        exact rec1078 1 151 (by decide) (by decide)
      · right
        exact rec1089 1 151 (by decide) (by decide)
      · right
        exact rec1100 1 151 (by decide) (by decide)
      · right
        exact rec1111 1 151 (by decide) (by decide)
      · right
        exact rec1122 1 151 (by decide) (by decide)
      · right
        exact rec1133 1 151 (by decide) (by decide)
      · right
        exact rec1144 1 151 (by decide) (by decide)
      · right
        exact rec1155 1 151 (by decide) (by decide)
      · right
        exact rec1166 1 151 (by decide) (by decide)
      · right
        exact rec1177 1 151 (by decide) (by decide)
      · right
        exact rec1188 1 151 (by decide) (by decide)
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
        exact rec1198 1 151 (by decide) (by decide)
      · right
        exact rec1205 1 151 (by decide) (by decide)
      · right
        exact rec1212 1 151 (by decide) (by decide)
      · right
        exact rec1219 1 151 (by decide) (by decide)
      · right
        exact rec1226 1 151 (by decide) (by decide)
      · right
        exact rec1233 1 151 (by decide) (by decide)
      · right
        exact rec1240 1 151 (by decide) (by decide)
      · right
        exact rec1247 1 151 (by decide) (by decide)
      · right
        exact rec1254 1 151 (by decide) (by decide)
      · right
        exact rec1261 1 151 (by decide) (by decide)
      · right
        exact rec1268 1 151 (by decide) (by decide)
      · right
        exact rec1275 1 151 (by decide) (by decide)
      · right
        exact rec1282 1 151 (by decide) (by decide)
      · right
        exact rec1289 1 151 (by decide) (by decide)
      · right
        exact rec1296 1 151 (by decide) (by decide)
      · right
        exact rec1303 1 151 (by decide) (by decide)
      · right
        exact rec1310 1 151 (by decide) (by decide)
      · right
        exact rec1317 1 151 (by decide) (by decide)
      · right
        exact rec1324 1 151 (by decide) (by decide)
      · right
        exact rec1331 1 151 (by decide) (by decide)
      · right
        exact rec1338 1 151 (by decide) (by decide)
      · right
        exact rec1345 1 151 (by decide) (by decide)
      · right
        exact rec1352 1 151 (by decide) (by decide)
      · right
        exact rec1359 1 151 (by decide) (by decide)
      · right
        exact rec1366 1 151 (by decide) (by decide)
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
        exact rec1376 1 151 (by decide) (by decide)
      · right
        exact rec1397 1 151 (by decide) (by decide)
      · right
        exact rec1421 1 151 (by decide) (by decide)
      · right
        exact rec1445 1 151 (by decide) (by decide)
      · right
        exact rec1469 1 151 (by decide) (by decide)
      · right
        exact rec1493 1 151 (by decide) (by decide)
      · right
        exact rec1514 1 151 (by decide) (by decide)
      · right
        exact rec1538 1 151 (by decide) (by decide)
      · right
        exact rec1562 1 151 (by decide) (by decide)
      · right
        exact rec1586 1 151 (by decide) (by decide)
      · right
        exact rec1610 1 151 (by decide) (by decide)
      · right
        exact rec1631 1 151 (by decide) (by decide)
      · right
        exact rec1655 1 151 (by decide) (by decide)
      · right
        exact rec1679 1 151 (by decide) (by decide)
      · right
        exact rec1703 1 151 (by decide) (by decide)
      · right
        exact rec1727 1 151 (by decide) (by decide)
      · right
        exact rec1748 1 151 (by decide) (by decide)
      · right
        exact rec1772 1 151 (by decide) (by decide)
      · right
        exact rec1796 1 151 (by decide) (by decide)
      · right
        exact rec1820 1 151 (by decide) (by decide)
      · right
        exact rec1844 1 151 (by decide) (by decide)
      · right
        exact rec1865 1 151 (by decide) (by decide)
      · right
        exact rec1889 1 151 (by decide) (by decide)
      · right
        exact rec1913 1 151 (by decide) (by decide)
      · right
        exact rec1937 1 151 (by decide) (by decide)
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
        exact rec1954 1 151 (by decide) (by decide)
      · right
        exact rec1970 1 151 (by decide) (by decide)
      · right
        exact rec1986 1 151 (by decide) (by decide)
      · right
        exact rec2002 1 151 (by decide) (by decide)
      · right
        exact rec2018 1 151 (by decide) (by decide)
      · right
        exact rec2034 1 151 (by decide) (by decide)
      · right
        exact rec2050 1 151 (by decide) (by decide)
      · right
        exact rec2066 1 151 (by decide) (by decide)
      · right
        exact rec2082 1 151 (by decide) (by decide)
      · right
        exact rec2098 1 151 (by decide) (by decide)
      · right
        exact rec2114 1 151 (by decide) (by decide)
      · right
        exact rec2130 1 151 (by decide) (by decide)
      · right
        exact rec2146 1 151 (by decide) (by decide)
      · right
        exact rec2162 1 151 (by decide) (by decide)
      · right
        exact rec2178 1 151 (by decide) (by decide)
      · right
        exact rec2194 1 151 (by decide) (by decide)
      · right
        exact rec2210 1 151 (by decide) (by decide)
      · right
        exact rec2226 1 151 (by decide) (by decide)
      · right
        exact rec2242 1 151 (by decide) (by decide)
      · right
        exact rec2258 1 151 (by decide) (by decide)
      · right
        exact rec2274 1 151 (by decide) (by decide)
      · right
        exact rec2290 1 151 (by decide) (by decide)
      · right
        exact rec2306 1 151 (by decide) (by decide)
      · right
        exact rec2322 1 151 (by decide) (by decide)
      · right
        exact rec2338 1 151 (by decide) (by decide)
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
        exact rec2354 1 151 (by decide) (by decide)
      · right
        exact rec2370 1 151 (by decide) (by decide)
      · right
        exact rec2384 1 151 (by decide) (by decide)
      · right
        exact rec2405 1 151 (by decide) (by decide)
      · right
        exact rec2429 1 151 (by decide) (by decide)
      · right
        exact rec2453 1 151 (by decide) (by decide)
      · right
        exact rec2477 1 151 (by decide) (by decide)
      · right
        exact rec2501 1 151 (by decide) (by decide)
      · right
        exact rec2525 1 151 (by decide) (by decide)
      · right
        exact rec2549 1 151 (by decide) (by decide)
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
        exact rec2572 1 151 (by decide) (by decide)
      · right
        exact rec2586 1 151 (by decide) (by decide)
      · right
        exact rec2599 1 151 (by decide) (by decide)
      · right
        exact rec2614 1 151 (by decide) (by decide)
      · right
        exact rec2620 1 151 (by decide) (by decide)
      · right
        exact rec2637 1 151 (by decide) (by decide)
      · right
        exact rec2650 1 151 (by decide) (by decide)
      · right
        exact rec2661 1 151 (by decide) (by decide)
      · right
        exact rec2673 1 151 (by decide) (by decide)
      · right
        exact rec2683 1 151 (by decide) (by decide)
      · right
        exact rec2691 1 151 (by decide) (by decide)
      · right
        exact rec2703 1 151 (by decide) (by decide)
      · right
        exact rec2705 1 151 (by decide) (by decide)
      · right
        exact rec2723 1 151 (by decide) (by decide)
      · right
        exact rec2730 1 151 (by decide) (by decide)
      · right
        exact rec2741 1 151 (by decide) (by decide)
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
        exact rec2751 1 151 (by decide) (by decide)
      · right
        exact rec2756 1 151 (by decide) (by decide)
      · right
        exact rec2762 1 151 (by decide) (by decide)
      · right
        exact rec2778 1 151 (by decide) (by decide)
      · right
        exact rec2788 1 151 (by decide) (by decide)
      · right
        exact rec2793 1 151 (by decide) (by decide)
      · right
        exact rec2798 1 151 (by decide) (by decide)
      · right
        exact rec2815 1 151 (by decide) (by decide)
      · right
        exact rec2825 1 151 (by decide) (by decide)
      · right
        exact rec2830 1 151 (by decide) (by decide)
      · right
        exact rec2835 1 151 (by decide) (by decide)
      · right
        exact rec2852 1 151 (by decide) (by decide)
      · right
        exact rec2862 1 151 (by decide) (by decide)
      · right
        exact rec2867 1 151 (by decide) (by decide)
      · right
        exact rec2872 1 151 (by decide) (by decide)
      · right
        exact rec2889 1 151 (by decide) (by decide)
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
        exact rec2905 1 151 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2915 1 151 (by decide) (by decide)
      · right
        exact rec2927 1 151 (by decide) (by decide)
      · right
        exact rec2939 1 151 (by decide) (by decide)
      · left
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
        exact rec2948 1 151 (by decide) (by decide)
      · right
        exact rec2964 1 151 (by decide) (by decide)
      · right
        exact rec2970 1 151 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2981 1 151 (by decide) (by decide)
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
    exact rec388 1 152 (by decide) (by decide)
  · left
    exact rec388 1 153 (by decide) (by decide)
  · left
    exact rec362 1 154 (by decide) (by decide)
  · left
    exact rec362 1 155 (by decide) (by decide)
  · left
    exact rec388 1 156 (by decide) (by decide)
  · left
    exact rec388 1 157 (by decide) (by decide)
  · left
    exact rec362 1 158 (by decide) (by decide)
  · left
    exact rec362 1 159 (by decide) (by decide)
end Section14Coverage_1_1_p144_160

end WorkReverseInterface_Freiman_workReverse20260919_s0001_coverage0001_parents_0144_0160


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_coverage0001_parents_0160_0176
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_1_1_p160_176
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec377 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[174],205⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[377]? = some (⟨16,(-1),[1,2,5,6,13,14],[174],205⟩) from rfl))
private theorem rec378 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([171, 187] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[171,187],206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[378]? = some (⟨16,(-1),[1,2,5,6,13,14],[171,187],206⟩) from rfl))
private theorem rec379 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([175] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[175],207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[379]? = some (⟨16,(-1),[1,2,5,6,13,14],[175],207⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec402 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,13],[170],205⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[402]? = some (⟨16,(-1),[1,13],[170],205⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0001_coverage0001_parents_0160_0176 : ∀ pl ∈ ((section14State section14Catalog 1).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 160).take 16, section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 1).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 160).take 16 = [⟨1,160,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,161,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,162,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,163,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,164,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,165,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,166,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,167,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,168,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,169,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,170,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨1,171,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨1,172,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,173,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,174,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,175,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec388 1 160 (by decide) (by decide)
  · left
    exact rec388 1 161 (by decide) (by decide)
  · left
    exact rec362 1 162 (by decide) (by decide)
  · left
    exact rec362 1 163 (by decide) (by decide)
  · left
    exact rec388 1 164 (by decide) (by decide)
  · left
    exact rec388 1 165 (by decide) (by decide)
  · left
    exact rec362 1 166 (by decide) (by decide)
  · left
    exact rec362 1 167 (by decide) (by decide)
  · left
    exact rec361 1 168 (by decide) (by decide)
  · left
    exact rec361 1 169 (by decide) (by decide)
  · left
    exact rec402 1 170 (by decide) (by decide)
  · left
    exact rec378 1 171 (by decide) (by decide)
  · left
    exact rec361 1 172 (by decide) (by decide)
  · left
    exact rec361 1 173 (by decide) (by decide)
  · left
    exact rec377 1 174 (by decide) (by decide)
  · left
    exact rec379 1 175 (by decide) (by decide)
end Section14Coverage_1_1_p160_176

end WorkReverseInterface_Freiman_workReverse20260919_s0001_coverage0001_parents_0160_0176


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_coverage0001_parents_0176_0192
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_1_1_p176_192
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
private theorem rec2577 (si parent : ℕ) (hs : si ∈ ([1, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[1,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[134]? = some (⟨33,(0),[1,13,14],[190],3⟩) from rfl))
private theorem rec2587 (si parent : ℕ) (hs : si ∈ ([1, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(1),[1,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[144]? = some (⟨33,(1),[1,13,14],[190],3⟩) from rfl))
private theorem rec2596 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(2),[1],[190],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[153]? = some (⟨33,(2),[1],[190],29⟩) from rfl))
private theorem rec2609 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,2,14],[190],234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[166]? = some (⟨33,(3),[1,2,14],[190],234⟩) from rfl))
private theorem rec2626 (si parent : ℕ) (hs : si ∈ ([1, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[183]? = some (⟨33,(4),[1,13,14],[190],3⟩) from rfl))
private theorem rec2638 (si parent : ℕ) (hs : si ∈ ([1, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[1,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[195]? = some (⟨33,(5),[1,13,14],[190],3⟩) from rfl))
private theorem rec2645 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1],[190],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[202]? = some (⟨33,(6),[1],[190],29⟩) from rfl))
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
theorem _root_.Freiman.workReverse20260919_s0001_coverage0001_parents_0176_0192 : ∀ pl ∈ ((section14State section14Catalog 1).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 176).take 16, section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 1).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 176).take 16 = [⟨1,176,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,177,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,178,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,179,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,180,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,181,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,182,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,183,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,184,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,185,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,186,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,187,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,188,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,189,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,190,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,191,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec388 1 176 (by decide) (by decide)
  · left
    exact rec388 1 177 (by decide) (by decide)
  · left
    exact rec362 1 178 (by decide) (by decide)
  · left
    exact rec362 1 179 (by decide) (by decide)
  · left
    exact rec388 1 180 (by decide) (by decide)
  · left
    exact rec388 1 181 (by decide) (by decide)
  · left
    exact rec362 1 182 (by decide) (by decide)
  · left
    exact rec362 1 183 (by decide) (by decide)
  · left
    exact rec361 1 184 (by decide) (by decide)
  · left
    exact rec361 1 185 (by decide) (by decide)
  · left
    exact rec380 1 186 (by decide) (by decide)
  · left
    exact rec378 1 187 (by decide) (by decide)
  · left
    exact rec361 1 188 (by decide) (by decide)
  · left
    exact rec361 1 189 (by decide) (by decide)
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
        exact rec495 1 190 (by decide) (by decide)
      · right
        exact rec512 1 190 (by decide) (by decide)
      · right
        exact rec529 1 190 (by decide) (by decide)
      · right
        exact rec546 1 190 (by decide) (by decide)
      · right
        exact rec563 1 190 (by decide) (by decide)
      · right
        exact rec580 1 190 (by decide) (by decide)
      · right
        exact rec597 1 190 (by decide) (by decide)
      · right
        exact rec614 1 190 (by decide) (by decide)
      · right
        exact rec631 1 190 (by decide) (by decide)
      · right
        exact rec648 1 190 (by decide) (by decide)
      · right
        exact rec665 1 190 (by decide) (by decide)
      · right
        exact rec682 1 190 (by decide) (by decide)
      · right
        exact rec699 1 190 (by decide) (by decide)
      · right
        exact rec716 1 190 (by decide) (by decide)
      · right
        exact rec733 1 190 (by decide) (by decide)
      · right
        exact rec750 1 190 (by decide) (by decide)
      · right
        exact rec767 1 190 (by decide) (by decide)
      · right
        exact rec784 1 190 (by decide) (by decide)
      · right
        exact rec801 1 190 (by decide) (by decide)
      · right
        exact rec818 1 190 (by decide) (by decide)
      · right
        exact rec835 1 190 (by decide) (by decide)
      · right
        exact rec852 1 190 (by decide) (by decide)
      · right
        exact rec869 1 190 (by decide) (by decide)
      · right
        exact rec886 1 190 (by decide) (by decide)
      · right
        exact rec903 1 190 (by decide) (by decide)
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
        exact rec921 1 190 (by decide) (by decide)
      · right
        exact rec932 1 190 (by decide) (by decide)
      · right
        exact rec943 1 190 (by decide) (by decide)
      · right
        exact rec954 1 190 (by decide) (by decide)
      · right
        exact rec965 1 190 (by decide) (by decide)
      · right
        exact rec976 1 190 (by decide) (by decide)
      · right
        exact rec987 1 190 (by decide) (by decide)
      · right
        exact rec998 1 190 (by decide) (by decide)
      · right
        exact rec1009 1 190 (by decide) (by decide)
      · right
        exact rec1020 1 190 (by decide) (by decide)
      · right
        exact rec1031 1 190 (by decide) (by decide)
      · right
        exact rec1042 1 190 (by decide) (by decide)
      · right
        exact rec1053 1 190 (by decide) (by decide)
      · right
        exact rec1064 1 190 (by decide) (by decide)
      · right
        exact rec1075 1 190 (by decide) (by decide)
      · right
        exact rec1086 1 190 (by decide) (by decide)
      · right
        exact rec1097 1 190 (by decide) (by decide)
      · right
        exact rec1108 1 190 (by decide) (by decide)
      · right
        exact rec1119 1 190 (by decide) (by decide)
      · right
        exact rec1130 1 190 (by decide) (by decide)
      · right
        exact rec1141 1 190 (by decide) (by decide)
      · right
        exact rec1152 1 190 (by decide) (by decide)
      · right
        exact rec1163 1 190 (by decide) (by decide)
      · right
        exact rec1174 1 190 (by decide) (by decide)
      · right
        exact rec1185 1 190 (by decide) (by decide)
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
        exact rec1195 1 190 (by decide) (by decide)
      · right
        exact rec1202 1 190 (by decide) (by decide)
      · right
        exact rec1209 1 190 (by decide) (by decide)
      · right
        exact rec1216 1 190 (by decide) (by decide)
      · right
        exact rec1223 1 190 (by decide) (by decide)
      · right
        exact rec1230 1 190 (by decide) (by decide)
      · right
        exact rec1237 1 190 (by decide) (by decide)
      · right
        exact rec1244 1 190 (by decide) (by decide)
      · right
        exact rec1251 1 190 (by decide) (by decide)
      · right
        exact rec1258 1 190 (by decide) (by decide)
      · right
        exact rec1265 1 190 (by decide) (by decide)
      · right
        exact rec1272 1 190 (by decide) (by decide)
      · right
        exact rec1279 1 190 (by decide) (by decide)
      · right
        exact rec1286 1 190 (by decide) (by decide)
      · right
        exact rec1293 1 190 (by decide) (by decide)
      · right
        exact rec1300 1 190 (by decide) (by decide)
      · right
        exact rec1307 1 190 (by decide) (by decide)
      · right
        exact rec1314 1 190 (by decide) (by decide)
      · right
        exact rec1321 1 190 (by decide) (by decide)
      · right
        exact rec1328 1 190 (by decide) (by decide)
      · right
        exact rec1335 1 190 (by decide) (by decide)
      · right
        exact rec1342 1 190 (by decide) (by decide)
      · right
        exact rec1349 1 190 (by decide) (by decide)
      · right
        exact rec1356 1 190 (by decide) (by decide)
      · right
        exact rec1363 1 190 (by decide) (by decide)
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
        exact rec1373 1 190 (by decide) (by decide)
      · right
        exact rec1394 1 190 (by decide) (by decide)
      · right
        exact rec1418 1 190 (by decide) (by decide)
      · right
        exact rec1442 1 190 (by decide) (by decide)
      · right
        exact rec1466 1 190 (by decide) (by decide)
      · right
        exact rec1490 1 190 (by decide) (by decide)
      · right
        exact rec1511 1 190 (by decide) (by decide)
      · right
        exact rec1535 1 190 (by decide) (by decide)
      · right
        exact rec1559 1 190 (by decide) (by decide)
      · right
        exact rec1583 1 190 (by decide) (by decide)
      · right
        exact rec1607 1 190 (by decide) (by decide)
      · right
        exact rec1628 1 190 (by decide) (by decide)
      · right
        exact rec1652 1 190 (by decide) (by decide)
      · right
        exact rec1676 1 190 (by decide) (by decide)
      · right
        exact rec1700 1 190 (by decide) (by decide)
      · right
        exact rec1724 1 190 (by decide) (by decide)
      · right
        exact rec1745 1 190 (by decide) (by decide)
      · right
        exact rec1769 1 190 (by decide) (by decide)
      · right
        exact rec1793 1 190 (by decide) (by decide)
      · right
        exact rec1817 1 190 (by decide) (by decide)
      · right
        exact rec1841 1 190 (by decide) (by decide)
      · right
        exact rec1862 1 190 (by decide) (by decide)
      · right
        exact rec1886 1 190 (by decide) (by decide)
      · right
        exact rec1910 1 190 (by decide) (by decide)
      · right
        exact rec1934 1 190 (by decide) (by decide)
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
        exact rec1956 1 190 (by decide) (by decide)
      · right
        exact rec1972 1 190 (by decide) (by decide)
      · right
        exact rec1988 1 190 (by decide) (by decide)
      · right
        exact rec2004 1 190 (by decide) (by decide)
      · right
        exact rec2020 1 190 (by decide) (by decide)
      · right
        exact rec2036 1 190 (by decide) (by decide)
      · right
        exact rec2052 1 190 (by decide) (by decide)
      · right
        exact rec2068 1 190 (by decide) (by decide)
      · right
        exact rec2084 1 190 (by decide) (by decide)
      · right
        exact rec2100 1 190 (by decide) (by decide)
      · right
        exact rec2116 1 190 (by decide) (by decide)
      · right
        exact rec2132 1 190 (by decide) (by decide)
      · right
        exact rec2148 1 190 (by decide) (by decide)
      · right
        exact rec2164 1 190 (by decide) (by decide)
      · right
        exact rec2180 1 190 (by decide) (by decide)
      · right
        exact rec2196 1 190 (by decide) (by decide)
      · right
        exact rec2212 1 190 (by decide) (by decide)
      · right
        exact rec2228 1 190 (by decide) (by decide)
      · right
        exact rec2244 1 190 (by decide) (by decide)
      · right
        exact rec2260 1 190 (by decide) (by decide)
      · right
        exact rec2276 1 190 (by decide) (by decide)
      · right
        exact rec2292 1 190 (by decide) (by decide)
      · right
        exact rec2308 1 190 (by decide) (by decide)
      · right
        exact rec2324 1 190 (by decide) (by decide)
      · right
        exact rec2340 1 190 (by decide) (by decide)
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
        exact rec2357 1 190 (by decide) (by decide)
      · right
        exact rec2372 1 190 (by decide) (by decide)
      · right
        exact rec2386 1 190 (by decide) (by decide)
      · right
        exact rec2409 1 190 (by decide) (by decide)
      · right
        exact rec2433 1 190 (by decide) (by decide)
      · right
        exact rec2457 1 190 (by decide) (by decide)
      · right
        exact rec2481 1 190 (by decide) (by decide)
      · right
        exact rec2505 1 190 (by decide) (by decide)
      · right
        exact rec2529 1 190 (by decide) (by decide)
      · right
        exact rec2553 1 190 (by decide) (by decide)
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
        exact rec2577 1 190 (by decide) (by decide)
      · right
        exact rec2587 1 190 (by decide) (by decide)
      · right
        exact rec2596 1 190 (by decide) (by decide)
      · right
        exact rec2609 1 190 (by decide) (by decide)
      · right
        exact rec2626 1 190 (by decide) (by decide)
      · right
        exact rec2638 1 190 (by decide) (by decide)
      · right
        exact rec2645 1 190 (by decide) (by decide)
      · right
        exact rec2656 1 190 (by decide) (by decide)
      · right
        exact rec2669 1 190 (by decide) (by decide)
      · right
        exact rec2679 1 190 (by decide) (by decide)
      · right
        exact rec2690 1 190 (by decide) (by decide)
      · right
        exact rec2700 1 190 (by decide) (by decide)
      · right
        exact rec2709 1 190 (by decide) (by decide)
      · right
        exact rec2721 1 190 (by decide) (by decide)
      · right
        exact rec2733 1 190 (by decide) (by decide)
      · right
        exact rec2744 1 190 (by decide) (by decide)
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
        exact rec2752 1 190 (by decide) (by decide)
      · right
        exact rec2757 1 190 (by decide) (by decide)
      · right
        exact rec2764 1 190 (by decide) (by decide)
      · right
        exact rec2780 1 190 (by decide) (by decide)
      · right
        exact rec2789 1 190 (by decide) (by decide)
      · right
        exact rec2794 1 190 (by decide) (by decide)
      · right
        exact rec2801 1 190 (by decide) (by decide)
      · right
        exact rec2817 1 190 (by decide) (by decide)
      · right
        exact rec2826 1 190 (by decide) (by decide)
      · right
        exact rec2831 1 190 (by decide) (by decide)
      · right
        exact rec2838 1 190 (by decide) (by decide)
      · right
        exact rec2854 1 190 (by decide) (by decide)
      · right
        exact rec2863 1 190 (by decide) (by decide)
      · right
        exact rec2868 1 190 (by decide) (by decide)
      · right
        exact rec2875 1 190 (by decide) (by decide)
      · right
        exact rec2891 1 190 (by decide) (by decide)
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
        exact rec2902 1 190 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2912 1 190 (by decide) (by decide)
      · right
        exact rec2922 1 190 (by decide) (by decide)
      · right
        exact rec2934 1 190 (by decide) (by decide)
      · left
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
        exact rec2952 1 190 (by decide) (by decide)
      · right
        exact rec2959 1 190 (by decide) (by decide)
      · right
        exact rec2973 1 190 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2983 1 190 (by decide) (by decide)
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
    exact rec381 1 191 (by decide) (by decide)
end Section14Coverage_1_1_p176_192

end WorkReverseInterface_Freiman_workReverse20260919_s0001_coverage0001_parents_0176_0192

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
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 1).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 128).take 64, section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j := by
  intro pl hpl
  let xs := section14Parents section14Catalog (section14State section14Catalog 1)
  let P := fun b : Section14Parent => section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j
  exact (all_of_interval_split P xs 128 160 192 (by decide) (by decide) (all_of_interval_split P xs 128 144 160 (by decide) (by decide) (Freiman.workReverse20260919_s0001_coverage0001_parents_0128_0144 pl hpl) (Freiman.workReverse20260919_s0001_coverage0001_parents_0144_0160 pl hpl)) (all_of_interval_split P xs 160 176 192 (by decide) (by decide) (Freiman.workReverse20260919_s0001_coverage0001_parents_0160_0176 pl hpl) (Freiman.workReverse20260919_s0001_coverage0001_parents_0176_0192 pl hpl)))

#print axioms solution
