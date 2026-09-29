-- Prove2me | solution 1 for Freiman.section14_s0013_coverage0003_parents_0240_0256
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T10:34:32.246726+00:00
-- url     : https://prove2.me/submissions/f47faf9e-462d-48f5-a6c7-5ffcdca0c2ce

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
namespace Section14Coverage_13_3_p240_256
private theorem rec4487 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[338]? = some (⟨60,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec4488 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[339]? = some (⟨60,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec4497 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([234, 250] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,13,14],[234,250],243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[348]? = some (⟨60,(-1),[1,2,5,6,13,14],[234,250],243⟩) from rfl))
private theorem rec4509 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 13, 14] : List ℕ)) (hp : parent ∈ ([235, 251] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,13,14],[235,251],243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[360]? = some (⟨60,(-1),[1,2,5,13,14],[235,251],243⟩) from rfl))
private theorem rec4514 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([254] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,13,14],[254],385⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[365]? = some (⟨60,(-1),[1,2,13,14],[254],385⟩) from rfl))
private theorem rec4526 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([255] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,13],[255],385⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[377]? = some (⟨60,(-1),[1,13],[255],385⟩) from rfl))
private theorem rec4603 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[454]? = some (⟨60,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 240).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 3).take 1 = [⟨4,60,[([1],[]),([2],[])],true,[(61,⟨([1],[]),true,([1],[]),false,false,[]⟩),(62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(65,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(66,⟨([2],[]),true,([2],[]),false,false,[]⟩),(67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(76,⟨([1],[]),true,([2],[]),false,false,[]⟩),(77,⟨([2],[]),true,([1],[]),false,false,[]⟩),(80,⟨([1],[]),true,([],[]),true,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 240).take 16 = [⟨1,240,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,241,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,242,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,243,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,244,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,245,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,246,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,247,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,248,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,249,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,250,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,251,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,252,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,253,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,254,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,255,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec4603 13 240 (by decide) (by decide)
  · left
    exact rec4603 13 241 (by decide) (by decide)
  · left
    exact rec4488 13 242 (by decide) (by decide)
  · left
    exact rec4488 13 243 (by decide) (by decide)
  · left
    exact rec4603 13 244 (by decide) (by decide)
  · left
    exact rec4603 13 245 (by decide) (by decide)
  · left
    exact rec4488 13 246 (by decide) (by decide)
  · left
    exact rec4488 13 247 (by decide) (by decide)
  · left
    exact rec4487 13 248 (by decide) (by decide)
  · left
    exact rec4487 13 249 (by decide) (by decide)
  · left
    exact rec4497 13 250 (by decide) (by decide)
  · left
    exact rec4509 13 251 (by decide) (by decide)
  · left
    exact rec4487 13 252 (by decide) (by decide)
  · left
    exact rec4487 13 253 (by decide) (by decide)
  · left
    exact rec4514 13 254 (by decide) (by decide)
  · left
    exact rec4526 13 255 (by decide) (by decide)
end Section14Coverage_13_3_p240_256

#print axioms solution
