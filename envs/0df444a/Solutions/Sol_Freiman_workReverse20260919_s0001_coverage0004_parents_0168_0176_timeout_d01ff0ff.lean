-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_coverage0004_parents_0168_0176_timeout_d01ff0ff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T22:53:00.335725+00:00
-- url     : https://prove2.me/submissions/1a4bf654-c24f-4931-a9b9-c2bc093f7269

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
namespace Section14Coverage_1_4_p168_176
private theorem rec5556 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[181]? = some (⟨82,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec5563 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 151, 171, 175, 187, 191] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],391⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[188]? = some (⟨82,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],391⟩) from rfl))
private theorem rec5565 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[1,2,5,6,13,14],[174],628⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[190]? = some (⟨82,(-1),[1,2,5,6,13,14],[174],628⟩) from rfl))
private theorem rec5618 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(0),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[243]? = some (⟨84,(0),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5620 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(1),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[245]? = some (⟨84,(1),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5622 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(2),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[247]? = some (⟨84,(2),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5624 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(3),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[249]? = some (⟨84,(3),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5626 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(4),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[251]? = some (⟨84,(4),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5628 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(5),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[253]? = some (⟨84,(5),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5630 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(6),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[255]? = some (⟨84,(6),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5632 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(7),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[257]? = some (⟨84,(7),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5634 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(8),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[259]? = some (⟨84,(8),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5636 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(9),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[261]? = some (⟨84,(9),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5638 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(10),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[263]? = some (⟨84,(10),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5640 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(11),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[265]? = some (⟨84,(11),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5642 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(12),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[267]? = some (⟨84,(12),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5644 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(13),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[269]? = some (⟨84,(13),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5646 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(14),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[271]? = some (⟨84,(14),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5648 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(15),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[273]? = some (⟨84,(15),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5650 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(16),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[275]? = some (⟨84,(16),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5652 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(17),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[277]? = some (⟨84,(17),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5654 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(18),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[279]? = some (⟨84,(18),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5656 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(19),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[281]? = some (⟨84,(19),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5658 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(20),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[283]? = some (⟨84,(20),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5660 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(21),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[285]? = some (⟨84,(21),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5662 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(22),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[287]? = some (⟨84,(22),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5664 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(23),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[289]? = some (⟨84,(23),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5666 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 84 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(24),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[291]? = some (⟨84,(24),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec5668 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(0),[1,5,6,13],[170],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[293]? = some (⟨86,(0),[1,5,6,13],[170],10⟩) from rfl))
private theorem rec5670 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(1),[1,5,6,13],[170],393⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[295]? = some (⟨86,(1),[1,5,6,13],[170],393⟩) from rfl))
private theorem rec5672 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(2),[1,5,6,13],[170],394⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[297]? = some (⟨86,(2),[1,5,6,13],[170],394⟩) from rfl))
private theorem rec5674 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(3),[1,5,6,13],[170],395⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[299]? = some (⟨86,(3),[1,5,6,13],[170],395⟩) from rfl))
private theorem rec5676 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(4),[1,5,6,13],[170],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[301]? = some (⟨86,(4),[1,5,6,13],[170],396⟩) from rfl))
private theorem rec5678 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(5),[1,5,6,13],[170],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[303]? = some (⟨86,(5),[1,5,6,13],[170],10⟩) from rfl))
private theorem rec5680 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(6),[1,5,6,13],[170],393⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[305]? = some (⟨86,(6),[1,5,6,13],[170],393⟩) from rfl))
private theorem rec5682 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(7),[1,5,6,13],[170],394⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[307]? = some (⟨86,(7),[1,5,6,13],[170],394⟩) from rfl))
private theorem rec5684 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(8),[1,5,6,13],[170],395⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[309]? = some (⟨86,(8),[1,5,6,13],[170],395⟩) from rfl))
private theorem rec5686 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(9),[1,5,6,13],[170],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[311]? = some (⟨86,(9),[1,5,6,13],[170],396⟩) from rfl))
private theorem rec5688 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(10),[1,5,6,13],[170],18⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[313]? = some (⟨86,(10),[1,5,6,13],[170],18⟩) from rfl))
private theorem rec5690 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(11),[1,5,6,13],[170],397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[315]? = some (⟨86,(11),[1,5,6,13],[170],397⟩) from rfl))
private theorem rec5692 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(12),[1,5,6,13],[170],397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[317]? = some (⟨86,(12),[1,5,6,13],[170],397⟩) from rfl))
private theorem rec5694 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(13),[1,5,6,13],[170],397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[319]? = some (⟨86,(13),[1,5,6,13],[170],397⟩) from rfl))
private theorem rec5696 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(14),[1,5,6,13],[170],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[321]? = some (⟨86,(14),[1,5,6,13],[170],396⟩) from rfl))
private theorem rec5698 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(15),[1,5,6,13],[170],21⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[323]? = some (⟨86,(15),[1,5,6,13],[170],21⟩) from rfl))
private theorem rec5700 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(16),[1,5,6,13],[170],398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[325]? = some (⟨86,(16),[1,5,6,13],[170],398⟩) from rfl))
private theorem rec5702 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(17),[1,5,6,13],[170],398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[327]? = some (⟨86,(17),[1,5,6,13],[170],398⟩) from rfl))
private theorem rec5704 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(18),[1,5,6,13],[170],398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[329]? = some (⟨86,(18),[1,5,6,13],[170],398⟩) from rfl))
private theorem rec5706 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(19),[1,5,6,13],[170],398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[331]? = some (⟨86,(19),[1,5,6,13],[170],398⟩) from rfl))
private theorem rec5708 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(20),[1,5,6,13],[170],24⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[333]? = some (⟨86,(20),[1,5,6,13],[170],24⟩) from rfl))
private theorem rec5710 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(21),[1,5,6,13],[170],399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[335]? = some (⟨86,(21),[1,5,6,13],[170],399⟩) from rfl))
private theorem rec5712 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(22),[1,5,6,13],[170],399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[337]? = some (⟨86,(22),[1,5,6,13],[170],399⟩) from rfl))
private theorem rec5714 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(23),[1,5,6,13],[170],399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[339]? = some (⟨86,(23),[1,5,6,13],[170],399⟩) from rfl))
private theorem rec5716 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 86 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨86,(24),[1,5,6,13],[170],399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[341]? = some (⟨86,(24),[1,5,6,13],[170],399⟩) from rfl))
private theorem rec5718 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(0),[1,5,6,13],[170],400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[343]? = some (⟨89,(0),[1,5,6,13],[170],400⟩) from rfl))
private theorem rec5721 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(1),[1,5,6,13],[170],401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[346]? = some (⟨89,(1),[1,5,6,13],[170],401⟩) from rfl))
private theorem rec5724 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(2),[1,5,6,13],[170],402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[349]? = some (⟨89,(2),[1,5,6,13],[170],402⟩) from rfl))
private theorem rec5727 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(3),[1,5,6,13],[170],403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[352]? = some (⟨89,(3),[1,5,6,13],[170],403⟩) from rfl))
private theorem rec5730 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(4),[1,5,6,13],[170],400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[355]? = some (⟨89,(4),[1,5,6,13],[170],400⟩) from rfl))
private theorem rec5733 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(5),[1,5,6,13],[170],401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[358]? = some (⟨89,(5),[1,5,6,13],[170],401⟩) from rfl))
private theorem rec5736 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(6),[1,5,6,13],[170],404⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[361]? = some (⟨89,(6),[1,5,6,13],[170],404⟩) from rfl))
private theorem rec5739 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(7),[1,5,6,13],[170],403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[364]? = some (⟨89,(7),[1,5,6,13],[170],403⟩) from rfl))
private theorem rec5742 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(8),[1,5,6,13],[170],400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[367]? = some (⟨89,(8),[1,5,6,13],[170],400⟩) from rfl))
private theorem rec5745 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(9),[1,5,6,13],[170],401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[370]? = some (⟨89,(9),[1,5,6,13],[170],401⟩) from rfl))
private theorem rec5748 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(10),[1,5,6,13],[170],402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[373]? = some (⟨89,(10),[1,5,6,13],[170],402⟩) from rfl))
private theorem rec5751 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(11),[1,5,6,13],[170],403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[376]? = some (⟨89,(11),[1,5,6,13],[170],403⟩) from rfl))
private theorem rec5754 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(12),[1,5,6,13],[170],400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[379]? = some (⟨89,(12),[1,5,6,13],[170],400⟩) from rfl))
private theorem rec5757 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(13),[1,5,6,13],[170],401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[382]? = some (⟨89,(13),[1,5,6,13],[170],401⟩) from rfl))
private theorem rec5760 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(14),[1,5,6,13],[170],405⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[385]? = some (⟨89,(14),[1,5,6,13],[170],405⟩) from rfl))
private theorem rec5763 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 89 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(15),[1,5,6,13],[170],403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[388]? = some (⟨89,(15),[1,5,6,13],[170],403⟩) from rfl))
private theorem rec5766 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(0),[1,5,6,13],[170],406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[391]? = some (⟨92,(0),[1,5,6,13],[170],406⟩) from rfl))
private theorem rec5769 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(1),[1,5,6,13],[170],407⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[394]? = some (⟨92,(1),[1,5,6,13],[170],407⟩) from rfl))
private theorem rec5772 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(2),[1,5,6,13],[170],406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[397]? = some (⟨92,(2),[1,5,6,13],[170],406⟩) from rfl))
private theorem rec5775 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(3),[1,5,6,13],[170],408⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[400]? = some (⟨92,(3),[1,5,6,13],[170],408⟩) from rfl))
private theorem rec5778 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(4),[1,5,6,13],[170],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[403]? = some (⟨92,(4),[1,5,6,13],[170],409⟩) from rfl))
private theorem rec5781 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(5),[1,5,6,13],[170],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[406]? = some (⟨92,(5),[1,5,6,13],[170],409⟩) from rfl))
private theorem rec5784 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(6),[1,5,6,13],[170],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[409]? = some (⟨92,(6),[1,5,6,13],[170],409⟩) from rfl))
private theorem rec5787 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(7),[1,5,6,13],[170],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[412]? = some (⟨92,(7),[1,5,6,13],[170],409⟩) from rfl))
private theorem rec5790 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(8),[1,5,6,13],[170],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[415]? = some (⟨92,(8),[1,5,6,13],[170],410⟩) from rfl))
private theorem rec5793 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(9),[1,5,6,13],[170],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[418]? = some (⟨92,(9),[1,5,6,13],[170],410⟩) from rfl))
private theorem rec5796 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(10),[1,5,6,13],[170],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[421]? = some (⟨92,(10),[1,5,6,13],[170],410⟩) from rfl))
private theorem rec5799 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(11),[1,5,6,13],[170],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[424]? = some (⟨92,(11),[1,5,6,13],[170],410⟩) from rfl))
private theorem rec5802 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(12),[1,5,6,13],[170],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[427]? = some (⟨92,(12),[1,5,6,13],[170],411⟩) from rfl))
private theorem rec5805 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(13),[1,5,6,13],[170],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[430]? = some (⟨92,(13),[1,5,6,13],[170],411⟩) from rfl))
private theorem rec5808 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(14),[1,5,6,13],[170],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[433]? = some (⟨92,(14),[1,5,6,13],[170],411⟩) from rfl))
private theorem rec5811 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 92 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(15),[1,5,6,13],[170],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[436]? = some (⟨92,(15),[1,5,6,13],[170],411⟩) from rfl))
private theorem rec5814 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(0),[1,5,6,13],[170],412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[439]? = some (⟨95,(0),[1,5,6,13],[170],412⟩) from rfl))
private theorem rec5817 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(1),[1,5,6,13],[170],412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[442]? = some (⟨95,(1),[1,5,6,13],[170],412⟩) from rfl))
private theorem rec5820 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(2),[1,5,6,13],[170],412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[445]? = some (⟨95,(2),[1,5,6,13],[170],412⟩) from rfl))
private theorem rec5823 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(3),[1,5,6,13],[170],412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[448]? = some (⟨95,(3),[1,5,6,13],[170],412⟩) from rfl))
private theorem rec5826 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(4),[1,5,6,13],[170],413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[451]? = some (⟨95,(4),[1,5,6,13],[170],413⟩) from rfl))
private theorem rec5829 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(5),[1,5,6,13],[170],413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[454]? = some (⟨95,(5),[1,5,6,13],[170],413⟩) from rfl))
private theorem rec5832 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(6),[1,5,6,13],[170],413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[457]? = some (⟨95,(6),[1,5,6,13],[170],413⟩) from rfl))
private theorem rec5835 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(7),[1,5,6,13],[170],413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[460]? = some (⟨95,(7),[1,5,6,13],[170],413⟩) from rfl))
private theorem rec5838 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(8),[1,5,6,13],[170],414⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[463]? = some (⟨95,(8),[1,5,6,13],[170],414⟩) from rfl))
private theorem rec5841 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(9),[1,5,6,13],[170],415⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[466]? = some (⟨95,(9),[1,5,6,13],[170],415⟩) from rfl))
private theorem rec5844 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(10),[1,5,6,13],[170],414⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[469]? = some (⟨95,(10),[1,5,6,13],[170],414⟩) from rfl))
private theorem rec5847 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(11),[1,5,6,13],[170],416⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[472]? = some (⟨95,(11),[1,5,6,13],[170],416⟩) from rfl))
private theorem rec5850 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(12),[1,5,6,13],[170],417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[475]? = some (⟨95,(12),[1,5,6,13],[170],417⟩) from rfl))
private theorem rec5853 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(13),[1,5,6,13],[170],417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[478]? = some (⟨95,(13),[1,5,6,13],[170],417⟩) from rfl))
private theorem rec5856 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(14),[1,5,6,13],[170],417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[481]? = some (⟨95,(14),[1,5,6,13],[170],417⟩) from rfl))
private theorem rec5859 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 95 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(15),[1,5,6,13],[170],417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[484]? = some (⟨95,(15),[1,5,6,13],[170],417⟩) from rfl))
private theorem rec5862 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(0),[1,5,6,13],[170],418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[487]? = some (⟨96,(0),[1,5,6,13],[170],418⟩) from rfl))
private theorem rec5865 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(1),[1,5,6,13],[170],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[490]? = some (⟨96,(1),[1,5,6,13],[170],419⟩) from rfl))
private theorem rec5868 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(2),[1,5,6,13],[170],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[493]? = some (⟨96,(2),[1,5,6,13],[170],420⟩) from rfl))
private theorem rec5871 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(3),[1,5,6,13],[170],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[496]? = some (⟨96,(3),[1,5,6,13],[170],421⟩) from rfl))
private theorem rec5874 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(4),[1,5,6,13],[170],422⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[499]? = some (⟨96,(4),[1,5,6,13],[170],422⟩) from rfl))
private theorem rec5877 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(5),[1,5,6,13],[170],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[502]? = some (⟨96,(5),[1,5,6,13],[170],419⟩) from rfl))
private theorem rec5880 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(6),[1,5,6,13],[170],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[505]? = some (⟨96,(6),[1,5,6,13],[170],420⟩) from rfl))
private theorem rec5883 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(7),[1,5,6,13],[170],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[508]? = some (⟨96,(7),[1,5,6,13],[170],421⟩) from rfl))
private theorem rec5886 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(8),[1,5,6,13],[170],418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[511]? = some (⟨96,(8),[1,5,6,13],[170],418⟩) from rfl))
private theorem rec5889 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(9),[1,5,6,13],[170],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[514]? = some (⟨96,(9),[1,5,6,13],[170],419⟩) from rfl))
private theorem rec5892 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(10),[1,5,6,13],[170],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[517]? = some (⟨96,(10),[1,5,6,13],[170],420⟩) from rfl))
private theorem rec5895 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(11),[1,5,6,13],[170],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[520]? = some (⟨96,(11),[1,5,6,13],[170],421⟩) from rfl))
private theorem rec5898 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(12),[1,5,6,13],[170],423⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[523]? = some (⟨96,(12),[1,5,6,13],[170],423⟩) from rfl))
private theorem rec5901 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(13),[1,5,6,13],[170],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[526]? = some (⟨96,(13),[1,5,6,13],[170],419⟩) from rfl))
private theorem rec5904 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(14),[1,5,6,13],[170],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[529]? = some (⟨96,(14),[1,5,6,13],[170],420⟩) from rfl))
private theorem rec5907 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 96 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(15),[1,5,6,13],[170],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[532]? = some (⟨96,(15),[1,5,6,13],[170],421⟩) from rfl))
private theorem rec5910 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 100 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨100,(0),[1,5,6,13],[170],424⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[535]? = some (⟨100,(0),[1,5,6,13],[170],424⟩) from rfl))
private theorem rec5913 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 100 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨100,(1),[1,5,6,13],[170],425⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[538]? = some (⟨100,(1),[1,5,6,13],[170],425⟩) from rfl))
private theorem rec5916 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 100 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨100,(2),[1,5,6,13],[170],426⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[541]? = some (⟨100,(2),[1,5,6,13],[170],426⟩) from rfl))
private theorem rec5919 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 100 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨100,(3),[1,5,6,13],[170],427⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[544]? = some (⟨100,(3),[1,5,6,13],[170],427⟩) from rfl))
private theorem rec5922 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(0),[1,5,6,13],[170],428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[547]? = some (⟨101,(0),[1,5,6,13],[170],428⟩) from rfl))
private theorem rec5925 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(1),[1,5,6,13],[170],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[550]? = some (⟨101,(1),[1,5,6,13],[170],429⟩) from rfl))
private theorem rec5928 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(2),[1,5,6,13],[170],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[553]? = some (⟨101,(2),[1,5,6,13],[170],430⟩) from rfl))
private theorem rec5931 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(3),[1,5,6,13],[170],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[556]? = some (⟨101,(3),[1,5,6,13],[170],431⟩) from rfl))
private theorem rec5934 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(4),[1,5,6,13],[170],432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[559]? = some (⟨101,(4),[1,5,6,13],[170],432⟩) from rfl))
private theorem rec5937 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(5),[1,5,6,13],[170],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[562]? = some (⟨101,(5),[1,5,6,13],[170],429⟩) from rfl))
private theorem rec5940 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(6),[1,5,6,13],[170],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[565]? = some (⟨101,(6),[1,5,6,13],[170],430⟩) from rfl))
private theorem rec5943 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(7),[1,5,6,13],[170],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[568]? = some (⟨101,(7),[1,5,6,13],[170],431⟩) from rfl))
private theorem rec5946 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(8),[1,5,6,13],[170],428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[571]? = some (⟨101,(8),[1,5,6,13],[170],428⟩) from rfl))
private theorem rec5949 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(9),[1,5,6,13],[170],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[574]? = some (⟨101,(9),[1,5,6,13],[170],429⟩) from rfl))
private theorem rec5952 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(10),[1,5,6,13],[170],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[577]? = some (⟨101,(10),[1,5,6,13],[170],430⟩) from rfl))
private theorem rec5955 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(11),[1,5,6,13],[170],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[580]? = some (⟨101,(11),[1,5,6,13],[170],431⟩) from rfl))
private theorem rec5958 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(12),[1,5,6,13],[170],433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[583]? = some (⟨101,(12),[1,5,6,13],[170],433⟩) from rfl))
private theorem rec5961 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(13),[1,5,6,13],[170],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[586]? = some (⟨101,(13),[1,5,6,13],[170],429⟩) from rfl))
private theorem rec5964 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(14),[1,5,6,13],[170],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[589]? = some (⟨101,(14),[1,5,6,13],[170],430⟩) from rfl))
private theorem rec5967 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 101 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(15),[1,5,6,13],[170],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[592]? = some (⟨101,(15),[1,5,6,13],[170],431⟩) from rfl))
private theorem rec5970 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(0),[1,5,6,13],[170],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[595]? = some (⟨104,(0),[1,5,6,13],[170],434⟩) from rfl))
private theorem rec5973 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(1),[1,5,6,13],[170],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[598]? = some (⟨104,(1),[1,5,6,13],[170],434⟩) from rfl))
private theorem rec5976 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(2),[1,5,6,13],[170],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[601]? = some (⟨104,(2),[1,5,6,13],[170],434⟩) from rfl))
private theorem rec5979 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(3),[1,5,6,13],[170],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[604]? = some (⟨104,(3),[1,5,6,13],[170],434⟩) from rfl))
private theorem rec5982 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(4),[1,5,6,13],[170],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[607]? = some (⟨104,(4),[1,5,6,13],[170],434⟩) from rfl))
private theorem rec5985 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(5),[1,5,6,13],[170],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[610]? = some (⟨104,(5),[1,5,6,13],[170],435⟩) from rfl))
private theorem rec5988 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(6),[1,5,6,13],[170],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[613]? = some (⟨104,(6),[1,5,6,13],[170],435⟩) from rfl))
private theorem rec5991 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(7),[1,5,6,13],[170],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[616]? = some (⟨104,(7),[1,5,6,13],[170],435⟩) from rfl))
private theorem rec5994 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(8),[1,5,6,13],[170],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[619]? = some (⟨104,(8),[1,5,6,13],[170],435⟩) from rfl))
private theorem rec5997 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(9),[1,5,6,13],[170],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[622]? = some (⟨104,(9),[1,5,6,13],[170],435⟩) from rfl))
private theorem rec6000 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(10),[1,5,6,13],[170],436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[625]? = some (⟨104,(10),[1,5,6,13],[170],436⟩) from rfl))
private theorem rec6003 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(11),[1,5,6,13],[170],437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[628]? = some (⟨104,(11),[1,5,6,13],[170],437⟩) from rfl))
private theorem rec6006 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(12),[1,5,6,13],[170],438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[631]? = some (⟨104,(12),[1,5,6,13],[170],438⟩) from rfl))
private theorem rec6009 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(13),[1,5,6,13],[170],437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[634]? = some (⟨104,(13),[1,5,6,13],[170],437⟩) from rfl))
private theorem rec6012 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(14),[1,5,6,13],[170],439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[637]? = some (⟨104,(14),[1,5,6,13],[170],439⟩) from rfl))
private theorem rec6015 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(15),[1,5,6,13],[170],436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[640]? = some (⟨104,(15),[1,5,6,13],[170],436⟩) from rfl))
private theorem rec6018 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(16),[1,5,6,13],[170],440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[643]? = some (⟨104,(16),[1,5,6,13],[170],440⟩) from rfl))
private theorem rec6021 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(17),[1,5,6,13],[170],440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[646]? = some (⟨104,(17),[1,5,6,13],[170],440⟩) from rfl))
private theorem rec6024 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(18),[1,5,6,13],[170],440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[649]? = some (⟨104,(18),[1,5,6,13],[170],440⟩) from rfl))
private theorem rec6027 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(19),[1,5,6,13],[170],440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[652]? = some (⟨104,(19),[1,5,6,13],[170],440⟩) from rfl))
private theorem rec6030 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(20),[1,5,6,13],[170],436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[655]? = some (⟨104,(20),[1,5,6,13],[170],436⟩) from rfl))
private theorem rec6033 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(21),[1,5,6,13],[170],437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[658]? = some (⟨104,(21),[1,5,6,13],[170],437⟩) from rfl))
private theorem rec6036 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(22),[1,5,6,13],[170],438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[661]? = some (⟨104,(22),[1,5,6,13],[170],438⟩) from rfl))
private theorem rec6039 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(23),[1,5,6,13],[170],437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[664]? = some (⟨104,(23),[1,5,6,13],[170],437⟩) from rfl))
private theorem rec6042 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 104 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(24),[1,5,6,13],[170],439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[667]? = some (⟨104,(24),[1,5,6,13],[170],439⟩) from rfl))
private theorem rec6045 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(0),[1,5,6,13],[170],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[670]? = some (⟨106,(0),[1,5,6,13],[170],441⟩) from rfl))
private theorem rec6048 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(1),[1,5,6,13],[170],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[673]? = some (⟨106,(1),[1,5,6,13],[170],442⟩) from rfl))
private theorem rec6051 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(2),[1,5,6,13],[170],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[676]? = some (⟨106,(2),[1,5,6,13],[170],441⟩) from rfl))
private theorem rec6054 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(3),[1,5,6,13],[170],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[679]? = some (⟨106,(3),[1,5,6,13],[170],443⟩) from rfl))
private theorem rec6057 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(4),[1,5,6,13],[170],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[682]? = some (⟨106,(4),[1,5,6,13],[170],444⟩) from rfl))
private theorem rec6060 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(5),[1,5,6,13],[170],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[685]? = some (⟨106,(5),[1,5,6,13],[170],441⟩) from rfl))
private theorem rec6063 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(6),[1,5,6,13],[170],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[688]? = some (⟨106,(6),[1,5,6,13],[170],442⟩) from rfl))
private theorem rec6066 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(7),[1,5,6,13],[170],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[691]? = some (⟨106,(7),[1,5,6,13],[170],441⟩) from rfl))
private theorem rec6069 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(8),[1,5,6,13],[170],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[694]? = some (⟨106,(8),[1,5,6,13],[170],443⟩) from rfl))
private theorem rec6072 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(9),[1,5,6,13],[170],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[697]? = some (⟨106,(9),[1,5,6,13],[170],444⟩) from rfl))
private theorem rec6075 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(10),[1,5,6,13],[170],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[700]? = some (⟨106,(10),[1,5,6,13],[170],445⟩) from rfl))
private theorem rec6078 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(11),[1,5,6,13],[170],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[703]? = some (⟨106,(11),[1,5,6,13],[170],445⟩) from rfl))
private theorem rec6081 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(12),[1,5,6,13],[170],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[706]? = some (⟨106,(12),[1,5,6,13],[170],445⟩) from rfl))
private theorem rec6084 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(13),[1,5,6,13],[170],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[709]? = some (⟨106,(13),[1,5,6,13],[170],445⟩) from rfl))
private theorem rec6087 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(14),[1,5,6,13],[170],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[712]? = some (⟨106,(14),[1,5,6,13],[170],444⟩) from rfl))
private theorem rec6090 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(15),[1,5,6,13],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[715]? = some (⟨106,(15),[1,5,6,13],[170],446⟩) from rfl))
private theorem rec6093 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(16),[1,5,6,13],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[718]? = some (⟨106,(16),[1,5,6,13],[170],446⟩) from rfl))
private theorem rec6096 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(17),[1,5,6,13],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[721]? = some (⟨106,(17),[1,5,6,13],[170],446⟩) from rfl))
private theorem rec6099 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(18),[1,5,6,13],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[724]? = some (⟨106,(18),[1,5,6,13],[170],446⟩) from rfl))
private theorem rec6102 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(19),[1,5,6,13],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[727]? = some (⟨106,(19),[1,5,6,13],[170],446⟩) from rfl))
private theorem rec6105 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(20),[1,5,6,13],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[730]? = some (⟨106,(20),[1,5,6,13],[170],447⟩) from rfl))
private theorem rec6108 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(21),[1,5,6,13],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[733]? = some (⟨106,(21),[1,5,6,13],[170],447⟩) from rfl))
private theorem rec6111 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(22),[1,5,6,13],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[736]? = some (⟨106,(22),[1,5,6,13],[170],447⟩) from rfl))
private theorem rec6114 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(23),[1,5,6,13],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[739]? = some (⟨106,(23),[1,5,6,13],[170],447⟩) from rfl))
private theorem rec6117 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 106 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(24),[1,5,6,13],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[742]? = some (⟨106,(24),[1,5,6,13],[170],447⟩) from rfl))
private theorem rec6120 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 109 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(0),[1,5,6,13],[170],448⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[745]? = some (⟨109,(0),[1,5,6,13],[170],448⟩) from rfl))
private theorem rec6123 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 109 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(1),[1,5,6,13],[170],448⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[748]? = some (⟨109,(1),[1,5,6,13],[170],448⟩) from rfl))
private theorem rec6126 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 109 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(2),[1,5,6,13],[170],449⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[751]? = some (⟨109,(2),[1,5,6,13],[170],449⟩) from rfl))
private theorem rec6129 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 109 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(3),[1,5,6,13],[170],449⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[754]? = some (⟨109,(3),[1,5,6,13],[170],449⟩) from rfl))
private theorem rec6132 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 109 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(4),[1,5,6,13],[170],450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[757]? = some (⟨109,(4),[1,5,6,13],[170],450⟩) from rfl))
private theorem rec6135 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 109 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(5),[1,5,6,13],[170],451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[760]? = some (⟨109,(5),[1,5,6,13],[170],451⟩) from rfl))
private theorem rec6138 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 109 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(6),[1,5,6,13],[170],450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[763]? = some (⟨109,(6),[1,5,6,13],[170],450⟩) from rfl))
private theorem rec6141 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 109 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(7),[1,5,6,13],[170],452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[766]? = some (⟨109,(7),[1,5,6,13],[170],452⟩) from rfl))
private theorem rec6144 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 109 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(8),[1,5,6,13],[170],450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[769]? = some (⟨109,(8),[1,5,6,13],[170],450⟩) from rfl))
private theorem rec6147 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 109 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(9),[1,5,6,13],[170],451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[772]? = some (⟨109,(9),[1,5,6,13],[170],451⟩) from rfl))
private theorem rec6150 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(0),[1,5,6,13],[170],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[775]? = some (⟨111,(0),[1,5,6,13],[170],453⟩) from rfl))
private theorem rec6153 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(1),[1,5,6,13],[170],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[778]? = some (⟨111,(1),[1,5,6,13],[170],454⟩) from rfl))
private theorem rec6156 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(2),[1,5,6,13],[170],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[781]? = some (⟨111,(2),[1,5,6,13],[170],453⟩) from rfl))
private theorem rec6159 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(3),[1,5,6,13],[170],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[784]? = some (⟨111,(3),[1,5,6,13],[170],455⟩) from rfl))
private theorem rec6162 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(4),[1,5,6,13],[170],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[787]? = some (⟨111,(4),[1,5,6,13],[170],456⟩) from rfl))
private theorem rec6165 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(5),[1,5,6,13],[170],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[790]? = some (⟨111,(5),[1,5,6,13],[170],453⟩) from rfl))
private theorem rec6168 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(6),[1,5,6,13],[170],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[793]? = some (⟨111,(6),[1,5,6,13],[170],454⟩) from rfl))
private theorem rec6171 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(7),[1,5,6,13],[170],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[796]? = some (⟨111,(7),[1,5,6,13],[170],453⟩) from rfl))
private theorem rec6174 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(8),[1,5,6,13],[170],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[799]? = some (⟨111,(8),[1,5,6,13],[170],455⟩) from rfl))
private theorem rec6177 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(9),[1,5,6,13],[170],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[802]? = some (⟨111,(9),[1,5,6,13],[170],456⟩) from rfl))
private theorem rec6180 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(10),[1,5,6,13],[170],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[805]? = some (⟨111,(10),[1,5,6,13],[170],457⟩) from rfl))
private theorem rec6183 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(11),[1,5,6,13],[170],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[808]? = some (⟨111,(11),[1,5,6,13],[170],457⟩) from rfl))
private theorem rec6186 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(12),[1,5,6,13],[170],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[811]? = some (⟨111,(12),[1,5,6,13],[170],457⟩) from rfl))
private theorem rec6189 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(13),[1,5,6,13],[170],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[814]? = some (⟨111,(13),[1,5,6,13],[170],457⟩) from rfl))
private theorem rec6192 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(14),[1,5,6,13],[170],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[817]? = some (⟨111,(14),[1,5,6,13],[170],456⟩) from rfl))
private theorem rec6195 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(15),[1,5,6,13],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[820]? = some (⟨111,(15),[1,5,6,13],[170],458⟩) from rfl))
private theorem rec6198 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(16),[1,5,6,13],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[823]? = some (⟨111,(16),[1,5,6,13],[170],458⟩) from rfl))
private theorem rec6201 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(17),[1,5,6,13],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[826]? = some (⟨111,(17),[1,5,6,13],[170],458⟩) from rfl))
private theorem rec6204 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(18),[1,5,6,13],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[829]? = some (⟨111,(18),[1,5,6,13],[170],458⟩) from rfl))
private theorem rec6207 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(19),[1,5,6,13],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[832]? = some (⟨111,(19),[1,5,6,13],[170],458⟩) from rfl))
private theorem rec6210 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(20),[1,5,6,13],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[835]? = some (⟨111,(20),[1,5,6,13],[170],459⟩) from rfl))
private theorem rec6213 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(21),[1,5,6,13],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[838]? = some (⟨111,(21),[1,5,6,13],[170],459⟩) from rfl))
private theorem rec6216 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(22),[1,5,6,13],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[841]? = some (⟨111,(22),[1,5,6,13],[170],459⟩) from rfl))
private theorem rec6219 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(23),[1,5,6,13],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[844]? = some (⟨111,(23),[1,5,6,13],[170],459⟩) from rfl))
private theorem rec6222 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 111 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(24),[1,5,6,13],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[847]? = some (⟨111,(24),[1,5,6,13],[170],459⟩) from rfl))
private theorem rec6225 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(0),[1,5,6,13],[170],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[850]? = some (⟨114,(0),[1,5,6,13],[170],460⟩) from rfl))
private theorem rec6228 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(1),[1,5,6,13],[170],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[853]? = some (⟨114,(1),[1,5,6,13],[170],460⟩) from rfl))
private theorem rec6231 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(2),[1,5,6,13],[170],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[856]? = some (⟨114,(2),[1,5,6,13],[170],460⟩) from rfl))
private theorem rec6234 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(3),[1,5,6,13],[170],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[859]? = some (⟨114,(3),[1,5,6,13],[170],460⟩) from rfl))
private theorem rec6237 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(4),[1,5,6,13],[170],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[862]? = some (⟨114,(4),[1,5,6,13],[170],460⟩) from rfl))
private theorem rec6240 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(5),[1,5,6,13],[170],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[865]? = some (⟨114,(5),[1,5,6,13],[170],461⟩) from rfl))
private theorem rec6243 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(6),[1,5,6,13],[170],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[868]? = some (⟨114,(6),[1,5,6,13],[170],461⟩) from rfl))
private theorem rec6246 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(7),[1,5,6,13],[170],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[871]? = some (⟨114,(7),[1,5,6,13],[170],461⟩) from rfl))
private theorem rec6249 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(8),[1,5,6,13],[170],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[874]? = some (⟨114,(8),[1,5,6,13],[170],461⟩) from rfl))
private theorem rec6252 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(9),[1,5,6,13],[170],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[877]? = some (⟨114,(9),[1,5,6,13],[170],461⟩) from rfl))
private theorem rec6255 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(10),[1,5,6,13],[170],462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[880]? = some (⟨114,(10),[1,5,6,13],[170],462⟩) from rfl))
private theorem rec6258 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(11),[1,5,6,13],[170],463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[883]? = some (⟨114,(11),[1,5,6,13],[170],463⟩) from rfl))
private theorem rec6261 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(12),[1,5,6,13],[170],464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[886]? = some (⟨114,(12),[1,5,6,13],[170],464⟩) from rfl))
private theorem rec6264 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(13),[1,5,6,13],[170],463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[889]? = some (⟨114,(13),[1,5,6,13],[170],463⟩) from rfl))
private theorem rec6267 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(14),[1,5,6,13],[170],465⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[892]? = some (⟨114,(14),[1,5,6,13],[170],465⟩) from rfl))
private theorem rec6270 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(15),[1,5,6,13],[170],462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[895]? = some (⟨114,(15),[1,5,6,13],[170],462⟩) from rfl))
private theorem rec6273 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(16),[1,5,6,13],[170],466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[898]? = some (⟨114,(16),[1,5,6,13],[170],466⟩) from rfl))
private theorem rec6276 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(17),[1,5,6,13],[170],466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[901]? = some (⟨114,(17),[1,5,6,13],[170],466⟩) from rfl))
private theorem rec6279 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(18),[1,5,6,13],[170],466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[904]? = some (⟨114,(18),[1,5,6,13],[170],466⟩) from rfl))
private theorem rec6282 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(19),[1,5,6,13],[170],466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[907]? = some (⟨114,(19),[1,5,6,13],[170],466⟩) from rfl))
private theorem rec6285 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(20),[1,5,6,13],[170],462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[910]? = some (⟨114,(20),[1,5,6,13],[170],462⟩) from rfl))
private theorem rec6288 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(21),[1,5,6,13],[170],463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[913]? = some (⟨114,(21),[1,5,6,13],[170],463⟩) from rfl))
private theorem rec6291 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(22),[1,5,6,13],[170],464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[916]? = some (⟨114,(22),[1,5,6,13],[170],464⟩) from rfl))
private theorem rec6294 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(23),[1,5,6,13],[170],463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[919]? = some (⟨114,(23),[1,5,6,13],[170],463⟩) from rfl))
private theorem rec6297 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 114 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(24),[1,5,6,13],[170],465⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[922]? = some (⟨114,(24),[1,5,6,13],[170],465⟩) from rfl))
private theorem rec6300 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(0),[1,5,6,13],[170],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[925]? = some (⟨116,(0),[1,5,6,13],[170],467⟩) from rfl))
private theorem rec6303 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(1),[1,5,6,13],[170],468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[928]? = some (⟨116,(1),[1,5,6,13],[170],468⟩) from rfl))
private theorem rec6306 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(2),[1,5,6,13],[170],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[931]? = some (⟨116,(2),[1,5,6,13],[170],467⟩) from rfl))
private theorem rec6309 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(3),[1,5,6,13],[170],469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[934]? = some (⟨116,(3),[1,5,6,13],[170],469⟩) from rfl))
private theorem rec6312 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(4),[1,5,6,13],[170],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[937]? = some (⟨116,(4),[1,5,6,13],[170],470⟩) from rfl))
private theorem rec6315 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(5),[1,5,6,13],[170],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[940]? = some (⟨116,(5),[1,5,6,13],[170],467⟩) from rfl))
private theorem rec6318 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(6),[1,5,6,13],[170],468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[943]? = some (⟨116,(6),[1,5,6,13],[170],468⟩) from rfl))
private theorem rec6321 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(7),[1,5,6,13],[170],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[946]? = some (⟨116,(7),[1,5,6,13],[170],467⟩) from rfl))
private theorem rec6324 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(8),[1,5,6,13],[170],469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[949]? = some (⟨116,(8),[1,5,6,13],[170],469⟩) from rfl))
private theorem rec6327 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(9),[1,5,6,13],[170],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[952]? = some (⟨116,(9),[1,5,6,13],[170],470⟩) from rfl))
private theorem rec6330 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(10),[1,5,6,13],[170],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[955]? = some (⟨116,(10),[1,5,6,13],[170],471⟩) from rfl))
private theorem rec6333 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(11),[1,5,6,13],[170],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[958]? = some (⟨116,(11),[1,5,6,13],[170],471⟩) from rfl))
private theorem rec6336 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(12),[1,5,6,13],[170],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[961]? = some (⟨116,(12),[1,5,6,13],[170],471⟩) from rfl))
private theorem rec6339 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(13),[1,5,6,13],[170],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[964]? = some (⟨116,(13),[1,5,6,13],[170],471⟩) from rfl))
private theorem rec6342 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(14),[1,5,6,13],[170],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[967]? = some (⟨116,(14),[1,5,6,13],[170],470⟩) from rfl))
private theorem rec6345 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(15),[1,5,6,13],[170],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[970]? = some (⟨116,(15),[1,5,6,13],[170],472⟩) from rfl))
private theorem rec6348 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(16),[1,5,6,13],[170],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[973]? = some (⟨116,(16),[1,5,6,13],[170],472⟩) from rfl))
private theorem rec6351 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(17),[1,5,6,13],[170],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[976]? = some (⟨116,(17),[1,5,6,13],[170],472⟩) from rfl))
private theorem rec6354 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(18),[1,5,6,13],[170],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[979]? = some (⟨116,(18),[1,5,6,13],[170],472⟩) from rfl))
private theorem rec6357 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(19),[1,5,6,13],[170],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[982]? = some (⟨116,(19),[1,5,6,13],[170],472⟩) from rfl))
private theorem rec6360 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(20),[1,5,6,13],[170],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[985]? = some (⟨116,(20),[1,5,6,13],[170],473⟩) from rfl))
private theorem rec6363 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(21),[1,5,6,13],[170],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[988]? = some (⟨116,(21),[1,5,6,13],[170],473⟩) from rfl))
private theorem rec6366 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(22),[1,5,6,13],[170],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[991]? = some (⟨116,(22),[1,5,6,13],[170],473⟩) from rfl))
private theorem rec6369 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(23),[1,5,6,13],[170],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[994]? = some (⟨116,(23),[1,5,6,13],[170],473⟩) from rfl))
private theorem rec6372 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 116 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(24),[1,5,6,13],[170],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[997]? = some (⟨116,(24),[1,5,6,13],[170],473⟩) from rfl))
private theorem rec6375 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(0),[1,5,6,13],[170],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1000]? = some (⟨119,(0),[1,5,6,13],[170],474⟩) from rfl))
private theorem rec6378 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(1),[1,5,6,13],[170],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1003]? = some (⟨119,(1),[1,5,6,13],[170],474⟩) from rfl))
private theorem rec6381 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(2),[1,5,6,13],[170],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1006]? = some (⟨119,(2),[1,5,6,13],[170],474⟩) from rfl))
private theorem rec6384 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(3),[1,5,6,13],[170],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1009]? = some (⟨119,(3),[1,5,6,13],[170],474⟩) from rfl))
private theorem rec6388 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(4),[1,5,6,13],[170],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1013]? = some (⟨119,(4),[1,5,6,13],[170],474⟩) from rfl))
private theorem rec6391 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(5),[1,5,6,13],[170],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1016]? = some (⟨119,(5),[1,5,6,13],[170],475⟩) from rfl))
private theorem rec6394 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(6),[1,5,6,13],[170],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1019]? = some (⟨119,(6),[1,5,6,13],[170],475⟩) from rfl))
private theorem rec6397 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(7),[1,5,6,13],[170],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1022]? = some (⟨119,(7),[1,5,6,13],[170],475⟩) from rfl))
private theorem rec6400 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(8),[1,5,6,13],[170],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1025]? = some (⟨119,(8),[1,5,6,13],[170],475⟩) from rfl))
private theorem rec6404 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(9),[1,5,6,13],[170],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1029]? = some (⟨119,(9),[1,5,6,13],[170],475⟩) from rfl))
private theorem rec6407 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(10),[1,5,6,13],[170],476⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1032]? = some (⟨119,(10),[1,5,6,13],[170],476⟩) from rfl))
private theorem rec6410 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(11),[1,5,6,13],[170],477⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1035]? = some (⟨119,(11),[1,5,6,13],[170],477⟩) from rfl))
private theorem rec6413 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(12),[1,5,6,13],[170],478⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1038]? = some (⟨119,(12),[1,5,6,13],[170],478⟩) from rfl))
private theorem rec6416 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(13),[1,5,6,13],[170],477⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1041]? = some (⟨119,(13),[1,5,6,13],[170],477⟩) from rfl))
private theorem rec6420 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(14),[1,5,6,13],[170],479⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1045]? = some (⟨119,(14),[1,5,6,13],[170],479⟩) from rfl))
private theorem rec6423 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(15),[1,5,6,13],[170],476⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1048]? = some (⟨119,(15),[1,5,6,13],[170],476⟩) from rfl))
private theorem rec6426 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(16),[1,5,6,13],[170],480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1051]? = some (⟨119,(16),[1,5,6,13],[170],480⟩) from rfl))
private theorem rec6429 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(17),[1,5,6,13],[170],480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1054]? = some (⟨119,(17),[1,5,6,13],[170],480⟩) from rfl))
private theorem rec6432 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(18),[1,5,6,13],[170],480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1057]? = some (⟨119,(18),[1,5,6,13],[170],480⟩) from rfl))
private theorem rec6436 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(19),[1,5,6,13],[170],480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1061]? = some (⟨119,(19),[1,5,6,13],[170],480⟩) from rfl))
private theorem rec6439 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(20),[1,5,6,13],[170],476⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1064]? = some (⟨119,(20),[1,5,6,13],[170],476⟩) from rfl))
private theorem rec6442 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(21),[1,5,6,13],[170],477⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1067]? = some (⟨119,(21),[1,5,6,13],[170],477⟩) from rfl))
private theorem rec6445 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(22),[1,5,6,13],[170],478⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1070]? = some (⟨119,(22),[1,5,6,13],[170],478⟩) from rfl))
private theorem rec6448 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(23),[1,5,6,13],[170],477⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1073]? = some (⟨119,(23),[1,5,6,13],[170],477⟩) from rfl))
private theorem rec6452 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 119 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(24),[1,5,6,13],[170],479⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1077]? = some (⟨119,(24),[1,5,6,13],[170],479⟩) from rfl))
private theorem rec6455 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(0),[1,5,6,13],[170],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1080]? = some (⟨121,(0),[1,5,6,13],[170],481⟩) from rfl))
private theorem rec6458 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(1),[1,5,6,13],[170],482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1083]? = some (⟨121,(1),[1,5,6,13],[170],482⟩) from rfl))
private theorem rec6461 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(2),[1,5,6,13],[170],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1086]? = some (⟨121,(2),[1,5,6,13],[170],481⟩) from rfl))
private theorem rec6464 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(3),[1,5,6,13],[170],483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1089]? = some (⟨121,(3),[1,5,6,13],[170],483⟩) from rfl))
private theorem rec6467 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(4),[1,5,6,13],[170],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1092]? = some (⟨121,(4),[1,5,6,13],[170],484⟩) from rfl))
private theorem rec6470 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(5),[1,5,6,13],[170],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1095]? = some (⟨121,(5),[1,5,6,13],[170],481⟩) from rfl))
private theorem rec6473 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(6),[1,5,6,13],[170],482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1098]? = some (⟨121,(6),[1,5,6,13],[170],482⟩) from rfl))
private theorem rec6476 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(7),[1,5,6,13],[170],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1101]? = some (⟨121,(7),[1,5,6,13],[170],481⟩) from rfl))
private theorem rec6479 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(8),[1,5,6,13],[170],483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1104]? = some (⟨121,(8),[1,5,6,13],[170],483⟩) from rfl))
private theorem rec6482 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(9),[1,5,6,13],[170],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1107]? = some (⟨121,(9),[1,5,6,13],[170],484⟩) from rfl))
private theorem rec6485 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(10),[1,5,6,13],[170],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1110]? = some (⟨121,(10),[1,5,6,13],[170],485⟩) from rfl))
private theorem rec6488 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(11),[1,5,6,13],[170],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1113]? = some (⟨121,(11),[1,5,6,13],[170],485⟩) from rfl))
private theorem rec6491 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(12),[1,5,6,13],[170],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1116]? = some (⟨121,(12),[1,5,6,13],[170],485⟩) from rfl))
private theorem rec6494 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(13),[1,5,6,13],[170],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1119]? = some (⟨121,(13),[1,5,6,13],[170],485⟩) from rfl))
private theorem rec6497 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(14),[1,5,6,13],[170],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1122]? = some (⟨121,(14),[1,5,6,13],[170],484⟩) from rfl))
private theorem rec6500 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(15),[1,5,6,13],[170],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1125]? = some (⟨121,(15),[1,5,6,13],[170],486⟩) from rfl))
private theorem rec6503 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(16),[1,5,6,13],[170],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1128]? = some (⟨121,(16),[1,5,6,13],[170],486⟩) from rfl))
private theorem rec6506 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(17),[1,5,6,13],[170],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1131]? = some (⟨121,(17),[1,5,6,13],[170],486⟩) from rfl))
private theorem rec6509 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(18),[1,5,6,13],[170],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1134]? = some (⟨121,(18),[1,5,6,13],[170],486⟩) from rfl))
private theorem rec6512 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(19),[1,5,6,13],[170],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1137]? = some (⟨121,(19),[1,5,6,13],[170],486⟩) from rfl))
private theorem rec6515 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(20),[1,5,6,13],[170],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1140]? = some (⟨121,(20),[1,5,6,13],[170],487⟩) from rfl))
private theorem rec6518 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(21),[1,5,6,13],[170],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1143]? = some (⟨121,(21),[1,5,6,13],[170],487⟩) from rfl))
private theorem rec6521 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(22),[1,5,6,13],[170],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1146]? = some (⟨121,(22),[1,5,6,13],[170],487⟩) from rfl))
private theorem rec6524 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(23),[1,5,6,13],[170],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1149]? = some (⟨121,(23),[1,5,6,13],[170],487⟩) from rfl))
private theorem rec6527 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 121 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(24),[1,5,6,13],[170],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1152]? = some (⟨121,(24),[1,5,6,13],[170],487⟩) from rfl))
private theorem rec6530 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(0),[1,5,6,13],[170],488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1155]? = some (⟨124,(0),[1,5,6,13],[170],488⟩) from rfl))
private theorem rec6533 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(1),[1,5,6,13],[170],489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1]? = some (⟨124,(1),[1,5,6,13],[170],489⟩) from rfl))
private theorem rec6536 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(2),[1,5,6,13],[170],490⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[4]? = some (⟨124,(2),[1,5,6,13],[170],490⟩) from rfl))
private theorem rec6539 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(3),[1,5,6,13],[170],491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[7]? = some (⟨124,(3),[1,5,6,13],[170],491⟩) from rfl))
private theorem rec6542 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(4),[1,5,6,13],[170],488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[10]? = some (⟨124,(4),[1,5,6,13],[170],488⟩) from rfl))
private theorem rec6545 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(5),[1,5,6,13],[170],489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[13]? = some (⟨124,(5),[1,5,6,13],[170],489⟩) from rfl))
private theorem rec6548 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(6),[1,5,6,13],[170],492⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[16]? = some (⟨124,(6),[1,5,6,13],[170],492⟩) from rfl))
private theorem rec6551 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(7),[1,5,6,13],[170],491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[19]? = some (⟨124,(7),[1,5,6,13],[170],491⟩) from rfl))
private theorem rec6554 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(8),[1,5,6,13],[170],488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[22]? = some (⟨124,(8),[1,5,6,13],[170],488⟩) from rfl))
private theorem rec6557 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(9),[1,5,6,13],[170],489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[25]? = some (⟨124,(9),[1,5,6,13],[170],489⟩) from rfl))
private theorem rec6560 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(10),[1,5,6,13],[170],490⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[28]? = some (⟨124,(10),[1,5,6,13],[170],490⟩) from rfl))
private theorem rec6563 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(11),[1,5,6,13],[170],491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[31]? = some (⟨124,(11),[1,5,6,13],[170],491⟩) from rfl))
private theorem rec6566 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(12),[1,5,6,13],[170],488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[34]? = some (⟨124,(12),[1,5,6,13],[170],488⟩) from rfl))
private theorem rec6569 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(13),[1,5,6,13],[170],489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[37]? = some (⟨124,(13),[1,5,6,13],[170],489⟩) from rfl))
private theorem rec6572 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(14),[1,5,6,13],[170],493⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[40]? = some (⟨124,(14),[1,5,6,13],[170],493⟩) from rfl))
private theorem rec6575 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 124 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(15),[1,5,6,13],[170],491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[43]? = some (⟨124,(15),[1,5,6,13],[170],491⟩) from rfl))
private theorem rec6578 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(0),[1,5,6,13],[170],494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[46]? = some (⟨127,(0),[1,5,6,13],[170],494⟩) from rfl))
private theorem rec6581 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(1),[1,5,6,13],[170],495⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[49]? = some (⟨127,(1),[1,5,6,13],[170],495⟩) from rfl))
private theorem rec6584 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(2),[1,5,6,13],[170],494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[52]? = some (⟨127,(2),[1,5,6,13],[170],494⟩) from rfl))
private theorem rec6587 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(3),[1,5,6,13],[170],496⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[55]? = some (⟨127,(3),[1,5,6,13],[170],496⟩) from rfl))
private theorem rec6590 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(4),[1,5,6,13],[170],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[58]? = some (⟨127,(4),[1,5,6,13],[170],497⟩) from rfl))
private theorem rec6593 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(5),[1,5,6,13],[170],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[61]? = some (⟨127,(5),[1,5,6,13],[170],497⟩) from rfl))
private theorem rec6596 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(6),[1,5,6,13],[170],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[64]? = some (⟨127,(6),[1,5,6,13],[170],497⟩) from rfl))
private theorem rec6599 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(7),[1,5,6,13],[170],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[67]? = some (⟨127,(7),[1,5,6,13],[170],497⟩) from rfl))
private theorem rec6602 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(8),[1,5,6,13],[170],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[70]? = some (⟨127,(8),[1,5,6,13],[170],498⟩) from rfl))
private theorem rec6605 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(9),[1,5,6,13],[170],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[73]? = some (⟨127,(9),[1,5,6,13],[170],498⟩) from rfl))
private theorem rec6608 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(10),[1,5,6,13],[170],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[76]? = some (⟨127,(10),[1,5,6,13],[170],498⟩) from rfl))
private theorem rec6611 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(11),[1,5,6,13],[170],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[79]? = some (⟨127,(11),[1,5,6,13],[170],498⟩) from rfl))
private theorem rec6614 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(12),[1,5,6,13],[170],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[82]? = some (⟨127,(12),[1,5,6,13],[170],499⟩) from rfl))
private theorem rec6617 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(13),[1,5,6,13],[170],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[85]? = some (⟨127,(13),[1,5,6,13],[170],499⟩) from rfl))
private theorem rec6620 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(14),[1,5,6,13],[170],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[88]? = some (⟨127,(14),[1,5,6,13],[170],499⟩) from rfl))
private theorem rec6623 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 127 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(15),[1,5,6,13],[170],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[91]? = some (⟨127,(15),[1,5,6,13],[170],499⟩) from rfl))
private theorem rec6626 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(0),[1,5,6],[170],500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[94]? = some (⟨129,(0),[1,5,6],[170],500⟩) from rfl))
private theorem rec6629 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(1),[1,5,6],[170],501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[97]? = some (⟨129,(1),[1,5,6],[170],501⟩) from rfl))
private theorem rec6632 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(2),[1,5,6],[170],502⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[100]? = some (⟨129,(2),[1,5,6],[170],502⟩) from rfl))
private theorem rec6635 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(3),[1,5,6],[170],503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[103]? = some (⟨129,(3),[1,5,6],[170],503⟩) from rfl))
private theorem rec6638 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(4),[1,5,6],[170],500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[106]? = some (⟨129,(4),[1,5,6],[170],500⟩) from rfl))
private theorem rec6641 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(5),[1,5,6],[170],501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[109]? = some (⟨129,(5),[1,5,6],[170],501⟩) from rfl))
private theorem rec6644 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(6),[1,5,6],[170],504⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[112]? = some (⟨129,(6),[1,5,6],[170],504⟩) from rfl))
private theorem rec6647 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(7),[1,5,6],[170],503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[115]? = some (⟨129,(7),[1,5,6],[170],503⟩) from rfl))
private theorem rec6650 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(8),[1,5,6],[170],500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[118]? = some (⟨129,(8),[1,5,6],[170],500⟩) from rfl))
private theorem rec6653 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(9),[1,5,6],[170],501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[121]? = some (⟨129,(9),[1,5,6],[170],501⟩) from rfl))
private theorem rec6656 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(10),[1,5,6],[170],502⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[124]? = some (⟨129,(10),[1,5,6],[170],502⟩) from rfl))
private theorem rec6659 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(11),[1,5,6],[170],503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[127]? = some (⟨129,(11),[1,5,6],[170],503⟩) from rfl))
private theorem rec6662 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(12),[1,5,6],[170],500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[130]? = some (⟨129,(12),[1,5,6],[170],500⟩) from rfl))
private theorem rec6665 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(13),[1,5,6],[170],501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[133]? = some (⟨129,(13),[1,5,6],[170],501⟩) from rfl))
private theorem rec6668 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(14),[1,5,6],[170],505⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[136]? = some (⟨129,(14),[1,5,6],[170],505⟩) from rfl))
private theorem rec6671 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 129 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(15),[1,5,6],[170],503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[139]? = some (⟨129,(15),[1,5,6],[170],503⟩) from rfl))
private theorem rec6674 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 132 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨132,(0),[1,5,6],[170],506⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[142]? = some (⟨132,(0),[1,5,6],[170],506⟩) from rfl))
private theorem rec6677 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 132 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨132,(1),[1,5,6],[170],507⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[145]? = some (⟨132,(1),[1,5,6],[170],507⟩) from rfl))
private theorem rec6680 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 132 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨132,(2),[1,5,6],[170],508⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[148]? = some (⟨132,(2),[1,5,6],[170],508⟩) from rfl))
private theorem rec6683 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 132 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨132,(3),[1,5,6],[170],509⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[151]? = some (⟨132,(3),[1,5,6],[170],509⟩) from rfl))
private theorem rec6686 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(0),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[154]? = some (⟨134,(0),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec6690 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(1),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[158]? = some (⟨134,(1),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec6693 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(2),[1,5,6,13],[170],510⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[161]? = some (⟨134,(2),[1,5,6,13],[170],510⟩) from rfl))
private theorem rec6696 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(3),[1,5,6,13],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[164]? = some (⟨134,(3),[1,5,6,13],[170],29⟩) from rfl))
private theorem rec6699 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(4),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[167]? = some (⟨134,(4),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec6702 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(5),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[170]? = some (⟨134,(5),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec6705 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(6),[1,5,6,13],[170],511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[173]? = some (⟨134,(6),[1,5,6,13],[170],511⟩) from rfl))
private theorem rec6708 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(7),[1,5,6,13],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[176]? = some (⟨134,(7),[1,5,6,13],[170],29⟩) from rfl))
private theorem rec6711 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(8),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[179]? = some (⟨134,(8),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec6714 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(9),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[182]? = some (⟨134,(9),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec6717 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(10),[1,5,6,13],[170],512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[185]? = some (⟨134,(10),[1,5,6,13],[170],512⟩) from rfl))
private theorem rec6720 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(11),[1,5,6,13],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[188]? = some (⟨134,(11),[1,5,6,13],[170],29⟩) from rfl))
private theorem rec6723 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(12),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[191]? = some (⟨134,(12),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec6726 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(13),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[194]? = some (⟨134,(13),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec6729 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(14),[1,5,6,13],[170],513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[197]? = some (⟨134,(14),[1,5,6,13],[170],513⟩) from rfl))
private theorem rec6732 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(15),[1,5,6,13],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[200]? = some (⟨134,(15),[1,5,6,13],[170],29⟩) from rfl))
private theorem rec6735 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(16),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[203]? = some (⟨134,(16),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec6738 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(17),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[206]? = some (⟨134,(17),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec6741 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(18),[1,5,6,13],[170],514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[209]? = some (⟨134,(18),[1,5,6,13],[170],514⟩) from rfl))
private theorem rec6744 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 134 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(19),[1,5,6,13],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[212]? = some (⟨134,(19),[1,5,6,13],[170],29⟩) from rfl))
private theorem rec6747 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(0),[1,5,6,13],[170],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[215]? = some (⟨135,(0),[1,5,6,13],[170],515⟩) from rfl))
private theorem rec6750 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(1),[1,5,6,13],[170],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[218]? = some (⟨135,(1),[1,5,6,13],[170],515⟩) from rfl))
private theorem rec6753 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(2),[1,5,6,13],[170],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[221]? = some (⟨135,(2),[1,5,6,13],[170],516⟩) from rfl))
private theorem rec6756 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(3),[1,5,6,13],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[224]? = some (⟨135,(3),[1,5,6,13],[170],517⟩) from rfl))
private theorem rec6759 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(4),[1,5,6,13],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[227]? = some (⟨135,(4),[1,5,6,13],[170],518⟩) from rfl))
private theorem rec6762 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(5),[1,5,6,13],[170],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[230]? = some (⟨135,(5),[1,5,6,13],[170],515⟩) from rfl))
private theorem rec6765 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(6),[1,5,6,13],[170],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[233]? = some (⟨135,(6),[1,5,6,13],[170],515⟩) from rfl))
private theorem rec6768 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(7),[1,5,6,13],[170],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[236]? = some (⟨135,(7),[1,5,6,13],[170],516⟩) from rfl))
private theorem rec6771 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(8),[1,5,6,13],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[239]? = some (⟨135,(8),[1,5,6,13],[170],517⟩) from rfl))
private theorem rec6774 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(9),[1,5,6,13],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[242]? = some (⟨135,(9),[1,5,6,13],[170],518⟩) from rfl))
private theorem rec6777 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(10),[1,5,6,13],[170],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[245]? = some (⟨135,(10),[1,5,6,13],[170],519⟩) from rfl))
private theorem rec6780 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(11),[1,5,6,13],[170],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[248]? = some (⟨135,(11),[1,5,6,13],[170],519⟩) from rfl))
private theorem rec6783 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(12),[1,5,6,13],[170],520⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[251]? = some (⟨135,(12),[1,5,6,13],[170],520⟩) from rfl))
private theorem rec6786 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(13),[1,5,6,13],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[254]? = some (⟨135,(13),[1,5,6,13],[170],517⟩) from rfl))
private theorem rec6789 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(14),[1,5,6,13],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[257]? = some (⟨135,(14),[1,5,6,13],[170],518⟩) from rfl))
private theorem rec6792 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(15),[1,5,6,13],[170],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[260]? = some (⟨135,(15),[1,5,6,13],[170],521⟩) from rfl))
private theorem rec6795 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(16),[1,5,6,13],[170],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[263]? = some (⟨135,(16),[1,5,6,13],[170],521⟩) from rfl))
private theorem rec6798 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(17),[1,5,6,13],[170],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[266]? = some (⟨135,(17),[1,5,6,13],[170],521⟩) from rfl))
private theorem rec6801 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(18),[1,5,6,13],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[269]? = some (⟨135,(18),[1,5,6,13],[170],517⟩) from rfl))
private theorem rec6806 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(19),[1,5,6,13],[170],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[274]? = some (⟨135,(19),[1,5,6,13],[170],521⟩) from rfl))
private theorem rec6809 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(20),[1,5,6,13],[170],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[277]? = some (⟨135,(20),[1,5,6,13],[170],522⟩) from rfl))
private theorem rec6812 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(21),[1,5,6,13],[170],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[280]? = some (⟨135,(21),[1,5,6,13],[170],522⟩) from rfl))
private theorem rec6815 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(22),[1,5,6,13],[170],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[283]? = some (⟨135,(22),[1,5,6,13],[170],522⟩) from rfl))
private theorem rec6818 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(23),[1,5,6,13],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[286]? = some (⟨135,(23),[1,5,6,13],[170],517⟩) from rfl))
private theorem rec6821 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 135 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(24),[1,5,6,13],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[289]? = some (⟨135,(24),[1,5,6,13],[170],518⟩) from rfl))
private theorem rec6826 (si parent : ℕ) (hs : si ∈ ([1, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(0),[1,6,13],[170],523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[294]? = some (⟨136,(0),[1,6,13],[170],523⟩) from rfl))
private theorem rec6830 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(1),[1,5,6,13],[170],524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[298]? = some (⟨136,(1),[1,5,6,13],[170],524⟩) from rfl))
private theorem rec6833 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(2),[1,5,6,13],[170],524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[301]? = some (⟨136,(2),[1,5,6,13],[170],524⟩) from rfl))
private theorem rec6836 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(3),[1,5,6,13],[170],524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[304]? = some (⟨136,(3),[1,5,6,13],[170],524⟩) from rfl))
private theorem rec6839 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(4),[1,5,6,13],[170],525⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[307]? = some (⟨136,(4),[1,5,6,13],[170],525⟩) from rfl))
private theorem rec6842 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(5),[1,5,6,13],[170],523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[310]? = some (⟨136,(5),[1,5,6,13],[170],523⟩) from rfl))
private theorem rec6845 (si parent : ℕ) (hs : si ∈ ([1, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(6),[1,6,13],[170],526⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[313]? = some (⟨136,(6),[1,6,13],[170],526⟩) from rfl))
private theorem rec6849 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(7),[1,5,6,13],[170],527⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[317]? = some (⟨136,(7),[1,5,6,13],[170],527⟩) from rfl))
private theorem rec6852 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(8),[1,5,6,13],[170],527⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[320]? = some (⟨136,(8),[1,5,6,13],[170],527⟩) from rfl))
private theorem rec6855 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(9),[1,5,6,13],[170],528⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[323]? = some (⟨136,(9),[1,5,6,13],[170],528⟩) from rfl))
private theorem rec6858 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(10),[1,5,6,13],[170],523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[326]? = some (⟨136,(10),[1,5,6,13],[170],523⟩) from rfl))
private theorem rec6861 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(11),[1,5,6,13],[170],526⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[329]? = some (⟨136,(11),[1,5,6,13],[170],526⟩) from rfl))
private theorem rec6864 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(12),[1,5,6,13],[170],529⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[332]? = some (⟨136,(12),[1,5,6,13],[170],529⟩) from rfl))
private theorem rec6867 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(13),[1,5,6,13],[170],530⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[335]? = some (⟨136,(13),[1,5,6,13],[170],530⟩) from rfl))
private theorem rec6870 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(14),[1,5,6,13],[170],531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[338]? = some (⟨136,(14),[1,5,6,13],[170],531⟩) from rfl))
private theorem rec6873 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(15),[1,5,6,13],[170],523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[341]? = some (⟨136,(15),[1,5,6,13],[170],523⟩) from rfl))
private theorem rec6876 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(16),[1,5,6,13],[170],526⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[344]? = some (⟨136,(16),[1,5,6,13],[170],526⟩) from rfl))
private theorem rec6879 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(17),[1,5,6,13],[170],532⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[347]? = some (⟨136,(17),[1,5,6,13],[170],532⟩) from rfl))
private theorem rec6882 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(18),[1,5,6,13],[170],533⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[350]? = some (⟨136,(18),[1,5,6,13],[170],533⟩) from rfl))
private theorem rec6885 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(19),[1,5,6,13],[170],534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[353]? = some (⟨136,(19),[1,5,6,13],[170],534⟩) from rfl))
private theorem rec6888 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(20),[1,5,6,13],[170],535⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[356]? = some (⟨136,(20),[1,5,6,13],[170],535⟩) from rfl))
private theorem rec6891 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(21),[1,5,6,13],[170],536⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[359]? = some (⟨136,(21),[1,5,6,13],[170],536⟩) from rfl))
private theorem rec6894 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(22),[1,5,6,13],[170],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[362]? = some (⟨136,(22),[1,5,6,13],[170],537⟩) from rfl))
private theorem rec6897 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(23),[1,5,6,13],[170],538⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[365]? = some (⟨136,(23),[1,5,6,13],[170],538⟩) from rfl))
private theorem rec6900 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 136 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(24),[1,5,6,13],[170],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[368]? = some (⟨136,(24),[1,5,6,13],[170],537⟩) from rfl))
private theorem rec6904 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(0),[1,5,6,13],[170],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[372]? = some (⟨138,(0),[1,5,6,13],[170],539⟩) from rfl))
private theorem rec6907 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(1),[1,5,6,13],[170],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[375]? = some (⟨138,(1),[1,5,6,13],[170],539⟩) from rfl))
private theorem rec6910 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(2),[1,5,6,13],[170],540⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[378]? = some (⟨138,(2),[1,5,6,13],[170],540⟩) from rfl))
private theorem rec6913 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(3),[1,5,6,13],[170],541⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[381]? = some (⟨138,(3),[1,5,6,13],[170],541⟩) from rfl))
private theorem rec6916 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(4),[1,5,6,13],[170],542⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[384]? = some (⟨138,(4),[1,5,6,13],[170],542⟩) from rfl))
private theorem rec6919 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(5),[1,5,6,13],[170],543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[387]? = some (⟨138,(5),[1,5,6,13],[170],543⟩) from rfl))
private theorem rec6923 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(6),[1,5,6,13],[170],543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[391]? = some (⟨138,(6),[1,5,6,13],[170],543⟩) from rfl))
private theorem rec6927 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(7),[1,5,6,13],[170],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[395]? = some (⟨138,(7),[1,5,6,13],[170],544⟩) from rfl))
private theorem rec6931 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(8),[1,5,6,13],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[399]? = some (⟨138,(8),[1,5,6,13],[170],517⟩) from rfl))
private theorem rec6935 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(9),[1,5,6,13],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[403]? = some (⟨138,(9),[1,5,6,13],[170],518⟩) from rfl))
private theorem rec6939 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(10),[1,5,6,13],[170],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[407]? = some (⟨138,(10),[1,5,6,13],[170],545⟩) from rfl))
private theorem rec6942 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(11),[1,5,6,13],[170],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[410]? = some (⟨138,(11),[1,5,6,13],[170],545⟩) from rfl))
private theorem rec6945 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(12),[1,5,6,13],[170],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[413]? = some (⟨138,(12),[1,5,6,13],[170],544⟩) from rfl))
private theorem rec6948 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(13),[1,5,6,13],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[416]? = some (⟨138,(13),[1,5,6,13],[170],517⟩) from rfl))
private theorem rec6951 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(14),[1,5,6,13],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[419]? = some (⟨138,(14),[1,5,6,13],[170],518⟩) from rfl))
private theorem rec6954 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(15),[1,5,6,13],[170],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[422]? = some (⟨138,(15),[1,5,6,13],[170],546⟩) from rfl))
private theorem rec6957 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(16),[1,5,6,13],[170],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[425]? = some (⟨138,(16),[1,5,6,13],[170],546⟩) from rfl))
private theorem rec6960 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(17),[1,5,6,13],[170],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[428]? = some (⟨138,(17),[1,5,6,13],[170],544⟩) from rfl))
private theorem rec6963 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(18),[1,5,6,13],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[431]? = some (⟨138,(18),[1,5,6,13],[170],517⟩) from rfl))
private theorem rec6966 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(19),[1,5,6,13],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[434]? = some (⟨138,(19),[1,5,6,13],[170],518⟩) from rfl))
private theorem rec6969 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(20),[1,5,6,13],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[437]? = some (⟨138,(20),[1,5,6,13],[170],547⟩) from rfl))
private theorem rec6972 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(21),[1,5,6,13],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[440]? = some (⟨138,(21),[1,5,6,13],[170],547⟩) from rfl))
private theorem rec6975 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(22),[1,5,6,13],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[443]? = some (⟨138,(22),[1,5,6,13],[170],547⟩) from rfl))
private theorem rec6978 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(23),[1,5,6,13],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[446]? = some (⟨138,(23),[1,5,6,13],[170],517⟩) from rfl))
private theorem rec6981 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 138 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(24),[1,5,6,13],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[449]? = some (⟨138,(24),[1,5,6,13],[170],518⟩) from rfl))
private theorem rec6984 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(0),[1,5,6,13],[170],548⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[452]? = some (⟨139,(0),[1,5,6,13],[170],548⟩) from rfl))
private theorem rec6987 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(1),[1,5,6,13],[170],549⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[455]? = some (⟨139,(1),[1,5,6,13],[170],549⟩) from rfl))
private theorem rec6990 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(2),[1,5,6,13],[170],548⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[458]? = some (⟨139,(2),[1,5,6,13],[170],548⟩) from rfl))
private theorem rec6993 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(3),[1,5,6,13],[170],550⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[461]? = some (⟨139,(3),[1,5,6,13],[170],550⟩) from rfl))
private theorem rec6996 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(4),[1,5,6,13],[170],551⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[464]? = some (⟨139,(4),[1,5,6,13],[170],551⟩) from rfl))
private theorem rec6999 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(5),[1,5,6,13],[170],552⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[467]? = some (⟨139,(5),[1,5,6,13],[170],552⟩) from rfl))
private theorem rec7003 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(6),[1,5,6,13],[170],553⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[471]? = some (⟨139,(6),[1,5,6,13],[170],553⟩) from rfl))
private theorem rec7007 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(7),[1,5,6,13],[170],554⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[475]? = some (⟨139,(7),[1,5,6,13],[170],554⟩) from rfl))
private theorem rec7011 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(8),[1,5,6,13],[170],555⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[479]? = some (⟨139,(8),[1,5,6,13],[170],555⟩) from rfl))
private theorem rec7014 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(9),[1,5,6,13],[170],556⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[482]? = some (⟨139,(9),[1,5,6,13],[170],556⟩) from rfl))
private theorem rec7017 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(10),[1,5,6,13],[170],557⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[485]? = some (⟨139,(10),[1,5,6,13],[170],557⟩) from rfl))
private theorem rec7020 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(11),[1,5,6,13],[170],558⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[488]? = some (⟨139,(11),[1,5,6,13],[170],558⟩) from rfl))
private theorem rec7023 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(12),[1,5,6,13],[170],559⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[491]? = some (⟨139,(12),[1,5,6,13],[170],559⟩) from rfl))
private theorem rec7026 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(13),[1,5,6,13],[170],560⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[494]? = some (⟨139,(13),[1,5,6,13],[170],560⟩) from rfl))
private theorem rec7029 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(14),[1,5,6,13],[170],561⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[497]? = some (⟨139,(14),[1,5,6,13],[170],561⟩) from rfl))
private theorem rec7032 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(15),[1,5,6,13],[170],562⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[500]? = some (⟨139,(15),[1,5,6,13],[170],562⟩) from rfl))
private theorem rec7035 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(16),[1,5,6,13],[170],555⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[503]? = some (⟨139,(16),[1,5,6,13],[170],555⟩) from rfl))
private theorem rec7038 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(17),[1,5,6,13],[170],556⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[506]? = some (⟨139,(17),[1,5,6,13],[170],556⟩) from rfl))
private theorem rec7041 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(18),[1,5,6,13],[170],557⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[509]? = some (⟨139,(18),[1,5,6,13],[170],557⟩) from rfl))
private theorem rec7044 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 139 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(19),[1,5,6,13],[170],558⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[512]? = some (⟨139,(19),[1,5,6,13],[170],558⟩) from rfl))
private theorem rec7047 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 140 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(0),[1,5,6,13],[170],563⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[515]? = some (⟨140,(0),[1,5,6,13],[170],563⟩) from rfl))
private theorem rec7050 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 140 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(1),[1,5,6,13],[170],564⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[518]? = some (⟨140,(1),[1,5,6,13],[170],564⟩) from rfl))
private theorem rec7053 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 140 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(2),[1,5,6,13],[170],565⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[521]? = some (⟨140,(2),[1,5,6,13],[170],565⟩) from rfl))
private theorem rec7056 (si parent : ℕ) (hs : si ∈ ([1, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 140 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(3),[1,6,13],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[524]? = some (⟨140,(3),[1,6,13],[170],547⟩) from rfl))
private theorem rec7061 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 140 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(4),[1,5,6,13],[170],566⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[529]? = some (⟨140,(4),[1,5,6,13],[170],566⟩) from rfl))
private theorem rec7064 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 140 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(5),[1,5,6,13],[170],564⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[532]? = some (⟨140,(5),[1,5,6,13],[170],564⟩) from rfl))
private theorem rec7067 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 140 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(6),[1,5,6,13],[170],567⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[535]? = some (⟨140,(6),[1,5,6,13],[170],567⟩) from rfl))
private theorem rec7072 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 140 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(7),[1,5,6,13],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[540]? = some (⟨140,(7),[1,5,6,13],[170],547⟩) from rfl))
private theorem rec7076 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(0),[1,5,6,13],[170],568⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[544]? = some (⟨142,(0),[1,5,6,13],[170],568⟩) from rfl))
private theorem rec7079 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(1),[1,5,6,13],[170],569⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[547]? = some (⟨142,(1),[1,5,6,13],[170],569⟩) from rfl))
private theorem rec7082 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(2),[1,5,6,13],[170],570⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[550]? = some (⟨142,(2),[1,5,6,13],[170],570⟩) from rfl))
private theorem rec7085 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(3),[1,5,6,13],[170],571⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[553]? = some (⟨142,(3),[1,5,6,13],[170],571⟩) from rfl))
private theorem rec7088 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(4),[1,5,6,13],[170],572⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[556]? = some (⟨142,(4),[1,5,6,13],[170],572⟩) from rfl))
private theorem rec7091 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(5),[1,5,6,13],[170],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[559]? = some (⟨142,(5),[1,5,6,13],[170],573⟩) from rfl))
private theorem rec7094 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(6),[1,5,6,13],[170],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[562]? = some (⟨142,(6),[1,5,6,13],[170],573⟩) from rfl))
private theorem rec7097 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(7),[1,5,6,13],[170],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[565]? = some (⟨142,(7),[1,5,6,13],[170],573⟩) from rfl))
private theorem rec7100 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(8),[1,5,6,13],[170],574⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[568]? = some (⟨142,(8),[1,5,6,13],[170],574⟩) from rfl))
private theorem rec7103 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(9),[1,5,6,13],[170],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[571]? = some (⟨142,(9),[1,5,6,13],[170],575⟩) from rfl))
private theorem rec7106 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(10),[1,5,6,13],[170],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[574]? = some (⟨142,(10),[1,5,6,13],[170],575⟩) from rfl))
private theorem rec7109 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(11),[1,5,6,13],[170],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[577]? = some (⟨142,(11),[1,5,6,13],[170],575⟩) from rfl))
private theorem rec7112 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(12),[1,5,6,13],[170],576⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[580]? = some (⟨142,(12),[1,5,6,13],[170],576⟩) from rfl))
private theorem rec7115 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(13),[1,5,6,13],[170],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[583]? = some (⟨142,(13),[1,5,6,13],[170],577⟩) from rfl))
private theorem rec7118 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(14),[1,5,6,13],[170],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[586]? = some (⟨142,(14),[1,5,6,13],[170],577⟩) from rfl))
private theorem rec7121 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 142 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(15),[1,5,6,13],[170],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[589]? = some (⟨142,(15),[1,5,6,13],[170],577⟩) from rfl))
private theorem rec7124 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(0),[1,5,6,13],[170],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[592]? = some (⟨143,(0),[1,5,6,13],[170],578⟩) from rfl))
private theorem rec7127 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(1),[1,5,6,13],[170],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[595]? = some (⟨143,(1),[1,5,6,13],[170],579⟩) from rfl))
private theorem rec7130 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(2),[1,5,6,13],[170],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[598]? = some (⟨143,(2),[1,5,6,13],[170],580⟩) from rfl))
private theorem rec7133 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(3),[1,5,6,13],[170],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[601]? = some (⟨143,(3),[1,5,6,13],[170],581⟩) from rfl))
private theorem rec7136 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(4),[1,5,6,13],[170],582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[604]? = some (⟨143,(4),[1,5,6,13],[170],582⟩) from rfl))
private theorem rec7139 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(5),[1,5,6,13],[170],583⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[607]? = some (⟨143,(5),[1,5,6,13],[170],583⟩) from rfl))
private theorem rec7142 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(6),[1,5,6,13],[170],584⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[610]? = some (⟨143,(6),[1,5,6,13],[170],584⟩) from rfl))
private theorem rec7145 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(7),[1,5,6,13],[170],585⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[613]? = some (⟨143,(7),[1,5,6,13],[170],585⟩) from rfl))
private theorem rec7148 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(8),[1,5,6,13],[170],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[616]? = some (⟨143,(8),[1,5,6,13],[170],578⟩) from rfl))
private theorem rec7151 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(9),[1,5,6,13],[170],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[619]? = some (⟨143,(9),[1,5,6,13],[170],579⟩) from rfl))
private theorem rec7154 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(10),[1,5,6,13],[170],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[622]? = some (⟨143,(10),[1,5,6,13],[170],580⟩) from rfl))
private theorem rec7157 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(11),[1,5,6,13],[170],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[625]? = some (⟨143,(11),[1,5,6,13],[170],581⟩) from rfl))
private theorem rec7160 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(12),[1,5,6,13],[170],586⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[628]? = some (⟨143,(12),[1,5,6,13],[170],586⟩) from rfl))
private theorem rec7163 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(13),[1,5,6,13],[170],587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[631]? = some (⟨143,(13),[1,5,6,13],[170],587⟩) from rfl))
private theorem rec7166 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(14),[1,5,6,13],[170],588⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[634]? = some (⟨143,(14),[1,5,6,13],[170],588⟩) from rfl))
private theorem rec7169 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 143 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(15),[1,5,6,13],[170],589⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[637]? = some (⟨143,(15),[1,5,6,13],[170],589⟩) from rfl))
private theorem rec7172 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 144 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨144,(0),[1,5,6,13],[170],590⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[640]? = some (⟨144,(0),[1,5,6,13],[170],590⟩) from rfl))
private theorem rec7175 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 144 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨144,(1),[1,5,6,13],[170],591⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[643]? = some (⟨144,(1),[1,5,6,13],[170],591⟩) from rfl))
private theorem rec7178 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 144 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨144,(2),[1,5,6,13],[170],590⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[646]? = some (⟨144,(2),[1,5,6,13],[170],590⟩) from rfl))
private theorem rec7181 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 144 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨144,(3),[1,5,6,13],[170],592⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[649]? = some (⟨144,(3),[1,5,6,13],[170],592⟩) from rfl))
private theorem rec7184 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(0),[1,5,6,13],[170],593⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[652]? = some (⟨145,(0),[1,5,6,13],[170],593⟩) from rfl))
private theorem rec7187 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(1),[1,5,6,13],[170],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[655]? = some (⟨145,(1),[1,5,6,13],[170],594⟩) from rfl))
private theorem rec7191 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(2),[1,5,6,13],[170],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[659]? = some (⟨145,(2),[1,5,6,13],[170],595⟩) from rfl))
private theorem rec7194 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(3),[1,5,6,13],[170],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[662]? = some (⟨145,(3),[1,5,6,13],[170],596⟩) from rfl))
private theorem rec7198 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(4),[1,5,6,13],[170],597⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[666]? = some (⟨145,(4),[1,5,6,13],[170],597⟩) from rfl))
private theorem rec7201 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(5),[1,5,6,13],[170],598⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[669]? = some (⟨145,(5),[1,5,6,13],[170],598⟩) from rfl))
private theorem rec7204 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(6),[1,5,6,13],[170],599⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[672]? = some (⟨145,(6),[1,5,6,13],[170],599⟩) from rfl))
private theorem rec7207 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(7),[1,5,6,13],[170],600⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[675]? = some (⟨145,(7),[1,5,6,13],[170],600⟩) from rfl))
private theorem rec7210 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(8),[1,5,6,13],[170],593⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[678]? = some (⟨145,(8),[1,5,6,13],[170],593⟩) from rfl))
private theorem rec7213 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(9),[1,5,6,13],[170],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[681]? = some (⟨145,(9),[1,5,6,13],[170],594⟩) from rfl))
private theorem rec7216 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(10),[1,5,6,13],[170],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[684]? = some (⟨145,(10),[1,5,6,13],[170],595⟩) from rfl))
private theorem rec7219 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(11),[1,5,6,13],[170],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[687]? = some (⟨145,(11),[1,5,6,13],[170],596⟩) from rfl))
private theorem rec7222 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(12),[1,5,6,13],[170],601⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[690]? = some (⟨145,(12),[1,5,6,13],[170],601⟩) from rfl))
private theorem rec7225 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(13),[1,5,6,13],[170],602⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[693]? = some (⟨145,(13),[1,5,6,13],[170],602⟩) from rfl))
private theorem rec7228 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(14),[1,5,6,13],[170],603⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[696]? = some (⟨145,(14),[1,5,6,13],[170],603⟩) from rfl))
private theorem rec7231 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 145 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(15),[1,5,6,13],[170],604⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[699]? = some (⟨145,(15),[1,5,6,13],[170],604⟩) from rfl))
private theorem rec7234 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(0),[1,5,6,13],[170],605⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[702]? = some (⟨146,(0),[1,5,6,13],[170],605⟩) from rfl))
private theorem rec7238 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(1),[1,5,6,13],[170],606⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[706]? = some (⟨146,(1),[1,5,6,13],[170],606⟩) from rfl))
private theorem rec7242 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(2),[1,5,6,13],[170],607⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[710]? = some (⟨146,(2),[1,5,6,13],[170],607⟩) from rfl))
private theorem rec7245 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(3),[1,5,6,13],[170],608⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[713]? = some (⟨146,(3),[1,5,6,13],[170],608⟩) from rfl))
private theorem rec7249 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(4),[1,5,6,13],[170],609⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[717]? = some (⟨146,(4),[1,5,6,13],[170],609⟩) from rfl))
private theorem rec7252 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(5),[1,5,6,13],[170],610⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[720]? = some (⟨146,(5),[1,5,6,13],[170],610⟩) from rfl))
private theorem rec7255 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(6),[1,5,6,13],[170],611⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[723]? = some (⟨146,(6),[1,5,6,13],[170],611⟩) from rfl))
private theorem rec7258 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(7),[1,5,6,13],[170],612⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[726]? = some (⟨146,(7),[1,5,6,13],[170],612⟩) from rfl))
private theorem rec7261 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(8),[1,5,6,13],[170],613⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[729]? = some (⟨146,(8),[1,5,6,13],[170],613⟩) from rfl))
private theorem rec7264 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(9),[1,5,6,13],[170],614⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[732]? = some (⟨146,(9),[1,5,6,13],[170],614⟩) from rfl))
private theorem rec7267 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(10),[1,5,6,13],[170],615⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[735]? = some (⟨146,(10),[1,5,6,13],[170],615⟩) from rfl))
private theorem rec7270 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(11),[1,5,6,13],[170],616⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[738]? = some (⟨146,(11),[1,5,6,13],[170],616⟩) from rfl))
private theorem rec7273 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(12),[1,5,6,13],[170],617⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[741]? = some (⟨146,(12),[1,5,6,13],[170],617⟩) from rfl))
private theorem rec7276 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(13),[1,5,6,13],[170],618⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[744]? = some (⟨146,(13),[1,5,6,13],[170],618⟩) from rfl))
private theorem rec7279 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(14),[1,5,6,13],[170],619⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[747]? = some (⟨146,(14),[1,5,6,13],[170],619⟩) from rfl))
private theorem rec7282 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 146 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(15),[1,5,6,13],[170],620⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[750]? = some (⟨146,(15),[1,5,6,13],[170],620⟩) from rfl))
private theorem rec7285 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(0),[1,5,6],[170],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[753]? = some (⟨150,(0),[1,5,6],[170],387⟩) from rfl))
private theorem rec7288 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(1),[1,5,6],[170],621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[756]? = some (⟨150,(1),[1,5,6],[170],621⟩) from rfl))
private theorem rec7291 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(2),[1,5,6],[170],622⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[759]? = some (⟨150,(2),[1,5,6],[170],622⟩) from rfl))
private theorem rec7294 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(3),[1,5,6],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[762]? = some (⟨150,(3),[1,5,6],[170],101⟩) from rfl))
private theorem rec7297 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(4),[1,5,6],[170],622⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[765]? = some (⟨150,(4),[1,5,6],[170],622⟩) from rfl))
private theorem rec7300 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(5),[1,5,6],[170],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[768]? = some (⟨150,(5),[1,5,6],[170],387⟩) from rfl))
private theorem rec7303 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(6),[1,5,6],[170],621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[771]? = some (⟨150,(6),[1,5,6],[170],621⟩) from rfl))
private theorem rec7306 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(7),[1,5,6],[170],623⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[774]? = some (⟨150,(7),[1,5,6],[170],623⟩) from rfl))
private theorem rec7309 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(8),[1,5,6],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[777]? = some (⟨150,(8),[1,5,6],[170],101⟩) from rfl))
private theorem rec7312 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(9),[1,5,6],[170],623⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[780]? = some (⟨150,(9),[1,5,6],[170],623⟩) from rfl))
private theorem rec7315 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(10),[1,5,6],[170],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[783]? = some (⟨150,(10),[1,5,6],[170],387⟩) from rfl))
private theorem rec7318 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(11),[1,5,6],[170],621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[786]? = some (⟨150,(11),[1,5,6],[170],621⟩) from rfl))
private theorem rec7321 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(12),[1,5,6],[170],624⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[789]? = some (⟨150,(12),[1,5,6],[170],624⟩) from rfl))
private theorem rec7324 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(13),[1,5,6],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[792]? = some (⟨150,(13),[1,5,6],[170],101⟩) from rfl))
private theorem rec7327 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(14),[1,5,6],[170],624⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[795]? = some (⟨150,(14),[1,5,6],[170],624⟩) from rfl))
private theorem rec7330 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(15),[1,5,6],[170],625⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[798]? = some (⟨150,(15),[1,5,6],[170],625⟩) from rfl))
private theorem rec7333 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(16),[1,5,6],[170],626⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[801]? = some (⟨150,(16),[1,5,6],[170],626⟩) from rfl))
private theorem rec7336 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(17),[1,5,6],[170],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[804]? = some (⟨150,(17),[1,5,6],[170],286⟩) from rfl))
private theorem rec7339 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(18),[1,5,6],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[807]? = some (⟨150,(18),[1,5,6],[170],101⟩) from rfl))
private theorem rec7342 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(19),[1,5,6],[170],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[810]? = some (⟨150,(19),[1,5,6],[170],286⟩) from rfl))
private theorem rec7345 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(20),[1,5,6],[170],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[813]? = some (⟨150,(20),[1,5,6],[170],387⟩) from rfl))
private theorem rec7348 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(21),[1,5,6],[170],621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[816]? = some (⟨150,(21),[1,5,6],[170],621⟩) from rfl))
private theorem rec7351 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(22),[1,5,6],[170],627⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[819]? = some (⟨150,(22),[1,5,6],[170],627⟩) from rfl))
private theorem rec7354 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(23),[1,5,6],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[822]? = some (⟨150,(23),[1,5,6],[170],101⟩) from rfl))
private theorem rec7357 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 150 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(24),[1,5,6],[170],627⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[825]? = some (⟨150,(24),[1,5,6],[170],627⟩) from rfl))
private theorem rec7360 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 151 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨151,(5),[1,5,6],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[828]? = some (⟨151,(5),[1,5,6],[170],3⟩) from rfl))
private theorem rec7362 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 151 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨151,(7),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[830]? = some (⟨151,(7),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec7363 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 151 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨151,(8),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[831]? = some (⟨151,(8),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec7364 (si parent : ℕ) (hs : si ∈ ([1] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 151 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨151,(9),[1],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[832]? = some (⟨151,(9),[1],[170],3⟩) from rfl))
private theorem rec7366 (si parent : ℕ) (hs : si ∈ ([1, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 151 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨151,(15),[1,6],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[834]? = some (⟨151,(15),[1,6],[170],3⟩) from rfl))
private theorem rec7368 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 151 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨151,(16),[1,5,6,13],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[836]? = some (⟨151,(16),[1,5,6,13],[170],3⟩) from rfl))
private theorem rec7369 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 151 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨151,(17),[1,5,6,13],[170],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[837]? = some (⟨151,(17),[1,5,6,13],[170],48⟩) from rfl))
private theorem rec7370 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 151 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨151,(19),[1,13],[170],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[838]? = some (⟨151,(19),[1,13],[170],48⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 1).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 168).take 8, section14Recorded section14Catalog 1 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 1).plans.drop 4).take 1 = [⟨5,82,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(83,⟨([1],[]),true,([1],[]),false,false,[]⟩),(84,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(85,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(86,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(87,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(88,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(89,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(90,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(91,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(92,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(93,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(94,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(95,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(96,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(97,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(98,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(99,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(100,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(101,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(102,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(103,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(104,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(105,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(106,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(107,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(108,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(109,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(110,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(111,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(112,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(113,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(114,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(115,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(116,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(117,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(118,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(119,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(120,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(121,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(122,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(123,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(124,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(125,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(126,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(127,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(128,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(129,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(130,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(131,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(132,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(133,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(134,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(135,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(136,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(137,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(138,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(139,⟨([3,2],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(140,⟨([3,1,1],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(141,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(142,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(143,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(144,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(145,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(146,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(147,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(148,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(149,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(150,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(151,⟨([1],[]),true,([],[]),true,false,[]⟩),(152,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 1)).drop 168).take 8 = [⟨1,168,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,169,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,170,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨1,171,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨1,172,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,173,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,174,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,175,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec5556 1 168 (by decide) (by decide)
  · left
    exact rec5556 1 169 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(83,⟨([1],[]),true,([1],[]),false,false,[]⟩),(84,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(85,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(86,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(87,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(88,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(89,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(90,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(91,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(92,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(93,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(94,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(95,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(96,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(97,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(98,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(99,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(100,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(101,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(102,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(103,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(104,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(105,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(106,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(107,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(108,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(109,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(110,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(111,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(112,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(113,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(114,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(115,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(116,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(117,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(118,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(119,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(120,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(121,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(122,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(123,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(124,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(125,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(126,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(127,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(128,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(129,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(130,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(131,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(132,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(133,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(134,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(135,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(136,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(137,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(138,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(139,⟨([3,2],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(140,⟨([3,1,1],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(141,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(142,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(143,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(144,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(145,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(146,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(147,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(148,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(149,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(150,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(151,⟨([1],[]),true,([],[]),true,false,[]⟩),(152,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 83)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 84)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5618 1 170 (by decide) (by decide)
      · right
        exact rec5620 1 170 (by decide) (by decide)
      · right
        exact rec5622 1 170 (by decide) (by decide)
      · right
        exact rec5624 1 170 (by decide) (by decide)
      · right
        exact rec5626 1 170 (by decide) (by decide)
      · right
        exact rec5628 1 170 (by decide) (by decide)
      · right
        exact rec5630 1 170 (by decide) (by decide)
      · right
        exact rec5632 1 170 (by decide) (by decide)
      · right
        exact rec5634 1 170 (by decide) (by decide)
      · right
        exact rec5636 1 170 (by decide) (by decide)
      · right
        exact rec5638 1 170 (by decide) (by decide)
      · right
        exact rec5640 1 170 (by decide) (by decide)
      · right
        exact rec5642 1 170 (by decide) (by decide)
      · right
        exact rec5644 1 170 (by decide) (by decide)
      · right
        exact rec5646 1 170 (by decide) (by decide)
      · right
        exact rec5648 1 170 (by decide) (by decide)
      · right
        exact rec5650 1 170 (by decide) (by decide)
      · right
        exact rec5652 1 170 (by decide) (by decide)
      · right
        exact rec5654 1 170 (by decide) (by decide)
      · right
        exact rec5656 1 170 (by decide) (by decide)
      · right
        exact rec5658 1 170 (by decide) (by decide)
      · right
        exact rec5660 1 170 (by decide) (by decide)
      · right
        exact rec5662 1 170 (by decide) (by decide)
      · right
        exact rec5664 1 170 (by decide) (by decide)
      · right
        exact rec5666 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 85)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 86)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5668 1 170 (by decide) (by decide)
      · right
        exact rec5670 1 170 (by decide) (by decide)
      · right
        exact rec5672 1 170 (by decide) (by decide)
      · right
        exact rec5674 1 170 (by decide) (by decide)
      · right
        exact rec5676 1 170 (by decide) (by decide)
      · right
        exact rec5678 1 170 (by decide) (by decide)
      · right
        exact rec5680 1 170 (by decide) (by decide)
      · right
        exact rec5682 1 170 (by decide) (by decide)
      · right
        exact rec5684 1 170 (by decide) (by decide)
      · right
        exact rec5686 1 170 (by decide) (by decide)
      · right
        exact rec5688 1 170 (by decide) (by decide)
      · right
        exact rec5690 1 170 (by decide) (by decide)
      · right
        exact rec5692 1 170 (by decide) (by decide)
      · right
        exact rec5694 1 170 (by decide) (by decide)
      · right
        exact rec5696 1 170 (by decide) (by decide)
      · right
        exact rec5698 1 170 (by decide) (by decide)
      · right
        exact rec5700 1 170 (by decide) (by decide)
      · right
        exact rec5702 1 170 (by decide) (by decide)
      · right
        exact rec5704 1 170 (by decide) (by decide)
      · right
        exact rec5706 1 170 (by decide) (by decide)
      · right
        exact rec5708 1 170 (by decide) (by decide)
      · right
        exact rec5710 1 170 (by decide) (by decide)
      · right
        exact rec5712 1 170 (by decide) (by decide)
      · right
        exact rec5714 1 170 (by decide) (by decide)
      · right
        exact rec5716 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 87)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 88)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 89)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5718 1 170 (by decide) (by decide)
      · right
        exact rec5721 1 170 (by decide) (by decide)
      · right
        exact rec5724 1 170 (by decide) (by decide)
      · right
        exact rec5727 1 170 (by decide) (by decide)
      · right
        exact rec5730 1 170 (by decide) (by decide)
      · right
        exact rec5733 1 170 (by decide) (by decide)
      · right
        exact rec5736 1 170 (by decide) (by decide)
      · right
        exact rec5739 1 170 (by decide) (by decide)
      · right
        exact rec5742 1 170 (by decide) (by decide)
      · right
        exact rec5745 1 170 (by decide) (by decide)
      · right
        exact rec5748 1 170 (by decide) (by decide)
      · right
        exact rec5751 1 170 (by decide) (by decide)
      · right
        exact rec5754 1 170 (by decide) (by decide)
      · right
        exact rec5757 1 170 (by decide) (by decide)
      · right
        exact rec5760 1 170 (by decide) (by decide)
      · right
        exact rec5763 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 90)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 91)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 92)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5766 1 170 (by decide) (by decide)
      · right
        exact rec5769 1 170 (by decide) (by decide)
      · right
        exact rec5772 1 170 (by decide) (by decide)
      · right
        exact rec5775 1 170 (by decide) (by decide)
      · right
        exact rec5778 1 170 (by decide) (by decide)
      · right
        exact rec5781 1 170 (by decide) (by decide)
      · right
        exact rec5784 1 170 (by decide) (by decide)
      · right
        exact rec5787 1 170 (by decide) (by decide)
      · right
        exact rec5790 1 170 (by decide) (by decide)
      · right
        exact rec5793 1 170 (by decide) (by decide)
      · right
        exact rec5796 1 170 (by decide) (by decide)
      · right
        exact rec5799 1 170 (by decide) (by decide)
      · right
        exact rec5802 1 170 (by decide) (by decide)
      · right
        exact rec5805 1 170 (by decide) (by decide)
      · right
        exact rec5808 1 170 (by decide) (by decide)
      · right
        exact rec5811 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 93)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 94)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 95)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5814 1 170 (by decide) (by decide)
      · right
        exact rec5817 1 170 (by decide) (by decide)
      · right
        exact rec5820 1 170 (by decide) (by decide)
      · right
        exact rec5823 1 170 (by decide) (by decide)
      · right
        exact rec5826 1 170 (by decide) (by decide)
      · right
        exact rec5829 1 170 (by decide) (by decide)
      · right
        exact rec5832 1 170 (by decide) (by decide)
      · right
        exact rec5835 1 170 (by decide) (by decide)
      · right
        exact rec5838 1 170 (by decide) (by decide)
      · right
        exact rec5841 1 170 (by decide) (by decide)
      · right
        exact rec5844 1 170 (by decide) (by decide)
      · right
        exact rec5847 1 170 (by decide) (by decide)
      · right
        exact rec5850 1 170 (by decide) (by decide)
      · right
        exact rec5853 1 170 (by decide) (by decide)
      · right
        exact rec5856 1 170 (by decide) (by decide)
      · right
        exact rec5859 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 96)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5862 1 170 (by decide) (by decide)
      · right
        exact rec5865 1 170 (by decide) (by decide)
      · right
        exact rec5868 1 170 (by decide) (by decide)
      · right
        exact rec5871 1 170 (by decide) (by decide)
      · right
        exact rec5874 1 170 (by decide) (by decide)
      · right
        exact rec5877 1 170 (by decide) (by decide)
      · right
        exact rec5880 1 170 (by decide) (by decide)
      · right
        exact rec5883 1 170 (by decide) (by decide)
      · right
        exact rec5886 1 170 (by decide) (by decide)
      · right
        exact rec5889 1 170 (by decide) (by decide)
      · right
        exact rec5892 1 170 (by decide) (by decide)
      · right
        exact rec5895 1 170 (by decide) (by decide)
      · right
        exact rec5898 1 170 (by decide) (by decide)
      · right
        exact rec5901 1 170 (by decide) (by decide)
      · right
        exact rec5904 1 170 (by decide) (by decide)
      · right
        exact rec5907 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 97)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 98)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 99)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 100)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5910 1 170 (by decide) (by decide)
      · right
        exact rec5913 1 170 (by decide) (by decide)
      · right
        exact rec5916 1 170 (by decide) (by decide)
      · right
        exact rec5919 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 101)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5922 1 170 (by decide) (by decide)
      · right
        exact rec5925 1 170 (by decide) (by decide)
      · right
        exact rec5928 1 170 (by decide) (by decide)
      · right
        exact rec5931 1 170 (by decide) (by decide)
      · right
        exact rec5934 1 170 (by decide) (by decide)
      · right
        exact rec5937 1 170 (by decide) (by decide)
      · right
        exact rec5940 1 170 (by decide) (by decide)
      · right
        exact rec5943 1 170 (by decide) (by decide)
      · right
        exact rec5946 1 170 (by decide) (by decide)
      · right
        exact rec5949 1 170 (by decide) (by decide)
      · right
        exact rec5952 1 170 (by decide) (by decide)
      · right
        exact rec5955 1 170 (by decide) (by decide)
      · right
        exact rec5958 1 170 (by decide) (by decide)
      · right
        exact rec5961 1 170 (by decide) (by decide)
      · right
        exact rec5964 1 170 (by decide) (by decide)
      · right
        exact rec5967 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 102)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 103)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 104)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5970 1 170 (by decide) (by decide)
      · right
        exact rec5973 1 170 (by decide) (by decide)
      · right
        exact rec5976 1 170 (by decide) (by decide)
      · right
        exact rec5979 1 170 (by decide) (by decide)
      · right
        exact rec5982 1 170 (by decide) (by decide)
      · right
        exact rec5985 1 170 (by decide) (by decide)
      · right
        exact rec5988 1 170 (by decide) (by decide)
      · right
        exact rec5991 1 170 (by decide) (by decide)
      · right
        exact rec5994 1 170 (by decide) (by decide)
      · right
        exact rec5997 1 170 (by decide) (by decide)
      · right
        exact rec6000 1 170 (by decide) (by decide)
      · right
        exact rec6003 1 170 (by decide) (by decide)
      · right
        exact rec6006 1 170 (by decide) (by decide)
      · right
        exact rec6009 1 170 (by decide) (by decide)
      · right
        exact rec6012 1 170 (by decide) (by decide)
      · right
        exact rec6015 1 170 (by decide) (by decide)
      · right
        exact rec6018 1 170 (by decide) (by decide)
      · right
        exact rec6021 1 170 (by decide) (by decide)
      · right
        exact rec6024 1 170 (by decide) (by decide)
      · right
        exact rec6027 1 170 (by decide) (by decide)
      · right
        exact rec6030 1 170 (by decide) (by decide)
      · right
        exact rec6033 1 170 (by decide) (by decide)
      · right
        exact rec6036 1 170 (by decide) (by decide)
      · right
        exact rec6039 1 170 (by decide) (by decide)
      · right
        exact rec6042 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 105)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 106)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6045 1 170 (by decide) (by decide)
      · right
        exact rec6048 1 170 (by decide) (by decide)
      · right
        exact rec6051 1 170 (by decide) (by decide)
      · right
        exact rec6054 1 170 (by decide) (by decide)
      · right
        exact rec6057 1 170 (by decide) (by decide)
      · right
        exact rec6060 1 170 (by decide) (by decide)
      · right
        exact rec6063 1 170 (by decide) (by decide)
      · right
        exact rec6066 1 170 (by decide) (by decide)
      · right
        exact rec6069 1 170 (by decide) (by decide)
      · right
        exact rec6072 1 170 (by decide) (by decide)
      · right
        exact rec6075 1 170 (by decide) (by decide)
      · right
        exact rec6078 1 170 (by decide) (by decide)
      · right
        exact rec6081 1 170 (by decide) (by decide)
      · right
        exact rec6084 1 170 (by decide) (by decide)
      · right
        exact rec6087 1 170 (by decide) (by decide)
      · right
        exact rec6090 1 170 (by decide) (by decide)
      · right
        exact rec6093 1 170 (by decide) (by decide)
      · right
        exact rec6096 1 170 (by decide) (by decide)
      · right
        exact rec6099 1 170 (by decide) (by decide)
      · right
        exact rec6102 1 170 (by decide) (by decide)
      · right
        exact rec6105 1 170 (by decide) (by decide)
      · right
        exact rec6108 1 170 (by decide) (by decide)
      · right
        exact rec6111 1 170 (by decide) (by decide)
      · right
        exact rec6114 1 170 (by decide) (by decide)
      · right
        exact rec6117 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 107)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 108)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 109)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6120 1 170 (by decide) (by decide)
      · right
        exact rec6123 1 170 (by decide) (by decide)
      · right
        exact rec6126 1 170 (by decide) (by decide)
      · right
        exact rec6129 1 170 (by decide) (by decide)
      · right
        exact rec6132 1 170 (by decide) (by decide)
      · right
        exact rec6135 1 170 (by decide) (by decide)
      · right
        exact rec6138 1 170 (by decide) (by decide)
      · right
        exact rec6141 1 170 (by decide) (by decide)
      · right
        exact rec6144 1 170 (by decide) (by decide)
      · right
        exact rec6147 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 110)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 111)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6150 1 170 (by decide) (by decide)
      · right
        exact rec6153 1 170 (by decide) (by decide)
      · right
        exact rec6156 1 170 (by decide) (by decide)
      · right
        exact rec6159 1 170 (by decide) (by decide)
      · right
        exact rec6162 1 170 (by decide) (by decide)
      · right
        exact rec6165 1 170 (by decide) (by decide)
      · right
        exact rec6168 1 170 (by decide) (by decide)
      · right
        exact rec6171 1 170 (by decide) (by decide)
      · right
        exact rec6174 1 170 (by decide) (by decide)
      · right
        exact rec6177 1 170 (by decide) (by decide)
      · right
        exact rec6180 1 170 (by decide) (by decide)
      · right
        exact rec6183 1 170 (by decide) (by decide)
      · right
        exact rec6186 1 170 (by decide) (by decide)
      · right
        exact rec6189 1 170 (by decide) (by decide)
      · right
        exact rec6192 1 170 (by decide) (by decide)
      · right
        exact rec6195 1 170 (by decide) (by decide)
      · right
        exact rec6198 1 170 (by decide) (by decide)
      · right
        exact rec6201 1 170 (by decide) (by decide)
      · right
        exact rec6204 1 170 (by decide) (by decide)
      · right
        exact rec6207 1 170 (by decide) (by decide)
      · right
        exact rec6210 1 170 (by decide) (by decide)
      · right
        exact rec6213 1 170 (by decide) (by decide)
      · right
        exact rec6216 1 170 (by decide) (by decide)
      · right
        exact rec6219 1 170 (by decide) (by decide)
      · right
        exact rec6222 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 112)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 113)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 114)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6225 1 170 (by decide) (by decide)
      · right
        exact rec6228 1 170 (by decide) (by decide)
      · right
        exact rec6231 1 170 (by decide) (by decide)
      · right
        exact rec6234 1 170 (by decide) (by decide)
      · right
        exact rec6237 1 170 (by decide) (by decide)
      · right
        exact rec6240 1 170 (by decide) (by decide)
      · right
        exact rec6243 1 170 (by decide) (by decide)
      · right
        exact rec6246 1 170 (by decide) (by decide)
      · right
        exact rec6249 1 170 (by decide) (by decide)
      · right
        exact rec6252 1 170 (by decide) (by decide)
      · right
        exact rec6255 1 170 (by decide) (by decide)
      · right
        exact rec6258 1 170 (by decide) (by decide)
      · right
        exact rec6261 1 170 (by decide) (by decide)
      · right
        exact rec6264 1 170 (by decide) (by decide)
      · right
        exact rec6267 1 170 (by decide) (by decide)
      · right
        exact rec6270 1 170 (by decide) (by decide)
      · right
        exact rec6273 1 170 (by decide) (by decide)
      · right
        exact rec6276 1 170 (by decide) (by decide)
      · right
        exact rec6279 1 170 (by decide) (by decide)
      · right
        exact rec6282 1 170 (by decide) (by decide)
      · right
        exact rec6285 1 170 (by decide) (by decide)
      · right
        exact rec6288 1 170 (by decide) (by decide)
      · right
        exact rec6291 1 170 (by decide) (by decide)
      · right
        exact rec6294 1 170 (by decide) (by decide)
      · right
        exact rec6297 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 115)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 116)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6300 1 170 (by decide) (by decide)
      · right
        exact rec6303 1 170 (by decide) (by decide)
      · right
        exact rec6306 1 170 (by decide) (by decide)
      · right
        exact rec6309 1 170 (by decide) (by decide)
      · right
        exact rec6312 1 170 (by decide) (by decide)
      · right
        exact rec6315 1 170 (by decide) (by decide)
      · right
        exact rec6318 1 170 (by decide) (by decide)
      · right
        exact rec6321 1 170 (by decide) (by decide)
      · right
        exact rec6324 1 170 (by decide) (by decide)
      · right
        exact rec6327 1 170 (by decide) (by decide)
      · right
        exact rec6330 1 170 (by decide) (by decide)
      · right
        exact rec6333 1 170 (by decide) (by decide)
      · right
        exact rec6336 1 170 (by decide) (by decide)
      · right
        exact rec6339 1 170 (by decide) (by decide)
      · right
        exact rec6342 1 170 (by decide) (by decide)
      · right
        exact rec6345 1 170 (by decide) (by decide)
      · right
        exact rec6348 1 170 (by decide) (by decide)
      · right
        exact rec6351 1 170 (by decide) (by decide)
      · right
        exact rec6354 1 170 (by decide) (by decide)
      · right
        exact rec6357 1 170 (by decide) (by decide)
      · right
        exact rec6360 1 170 (by decide) (by decide)
      · right
        exact rec6363 1 170 (by decide) (by decide)
      · right
        exact rec6366 1 170 (by decide) (by decide)
      · right
        exact rec6369 1 170 (by decide) (by decide)
      · right
        exact rec6372 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 117)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 118)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 119)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6375 1 170 (by decide) (by decide)
      · right
        exact rec6378 1 170 (by decide) (by decide)
      · right
        exact rec6381 1 170 (by decide) (by decide)
      · right
        exact rec6384 1 170 (by decide) (by decide)
      · right
        exact rec6388 1 170 (by decide) (by decide)
      · right
        exact rec6391 1 170 (by decide) (by decide)
      · right
        exact rec6394 1 170 (by decide) (by decide)
      · right
        exact rec6397 1 170 (by decide) (by decide)
      · right
        exact rec6400 1 170 (by decide) (by decide)
      · right
        exact rec6404 1 170 (by decide) (by decide)
      · right
        exact rec6407 1 170 (by decide) (by decide)
      · right
        exact rec6410 1 170 (by decide) (by decide)
      · right
        exact rec6413 1 170 (by decide) (by decide)
      · right
        exact rec6416 1 170 (by decide) (by decide)
      · right
        exact rec6420 1 170 (by decide) (by decide)
      · right
        exact rec6423 1 170 (by decide) (by decide)
      · right
        exact rec6426 1 170 (by decide) (by decide)
      · right
        exact rec6429 1 170 (by decide) (by decide)
      · right
        exact rec6432 1 170 (by decide) (by decide)
      · right
        exact rec6436 1 170 (by decide) (by decide)
      · right
        exact rec6439 1 170 (by decide) (by decide)
      · right
        exact rec6442 1 170 (by decide) (by decide)
      · right
        exact rec6445 1 170 (by decide) (by decide)
      · right
        exact rec6448 1 170 (by decide) (by decide)
      · right
        exact rec6452 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 120)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 121)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6455 1 170 (by decide) (by decide)
      · right
        exact rec6458 1 170 (by decide) (by decide)
      · right
        exact rec6461 1 170 (by decide) (by decide)
      · right
        exact rec6464 1 170 (by decide) (by decide)
      · right
        exact rec6467 1 170 (by decide) (by decide)
      · right
        exact rec6470 1 170 (by decide) (by decide)
      · right
        exact rec6473 1 170 (by decide) (by decide)
      · right
        exact rec6476 1 170 (by decide) (by decide)
      · right
        exact rec6479 1 170 (by decide) (by decide)
      · right
        exact rec6482 1 170 (by decide) (by decide)
      · right
        exact rec6485 1 170 (by decide) (by decide)
      · right
        exact rec6488 1 170 (by decide) (by decide)
      · right
        exact rec6491 1 170 (by decide) (by decide)
      · right
        exact rec6494 1 170 (by decide) (by decide)
      · right
        exact rec6497 1 170 (by decide) (by decide)
      · right
        exact rec6500 1 170 (by decide) (by decide)
      · right
        exact rec6503 1 170 (by decide) (by decide)
      · right
        exact rec6506 1 170 (by decide) (by decide)
      · right
        exact rec6509 1 170 (by decide) (by decide)
      · right
        exact rec6512 1 170 (by decide) (by decide)
      · right
        exact rec6515 1 170 (by decide) (by decide)
      · right
        exact rec6518 1 170 (by decide) (by decide)
      · right
        exact rec6521 1 170 (by decide) (by decide)
      · right
        exact rec6524 1 170 (by decide) (by decide)
      · right
        exact rec6527 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 122)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 123)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 124)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6530 1 170 (by decide) (by decide)
      · right
        exact rec6533 1 170 (by decide) (by decide)
      · right
        exact rec6536 1 170 (by decide) (by decide)
      · right
        exact rec6539 1 170 (by decide) (by decide)
      · right
        exact rec6542 1 170 (by decide) (by decide)
      · right
        exact rec6545 1 170 (by decide) (by decide)
      · right
        exact rec6548 1 170 (by decide) (by decide)
      · right
        exact rec6551 1 170 (by decide) (by decide)
      · right
        exact rec6554 1 170 (by decide) (by decide)
      · right
        exact rec6557 1 170 (by decide) (by decide)
      · right
        exact rec6560 1 170 (by decide) (by decide)
      · right
        exact rec6563 1 170 (by decide) (by decide)
      · right
        exact rec6566 1 170 (by decide) (by decide)
      · right
        exact rec6569 1 170 (by decide) (by decide)
      · right
        exact rec6572 1 170 (by decide) (by decide)
      · right
        exact rec6575 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 125)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 126)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 127)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6578 1 170 (by decide) (by decide)
      · right
        exact rec6581 1 170 (by decide) (by decide)
      · right
        exact rec6584 1 170 (by decide) (by decide)
      · right
        exact rec6587 1 170 (by decide) (by decide)
      · right
        exact rec6590 1 170 (by decide) (by decide)
      · right
        exact rec6593 1 170 (by decide) (by decide)
      · right
        exact rec6596 1 170 (by decide) (by decide)
      · right
        exact rec6599 1 170 (by decide) (by decide)
      · right
        exact rec6602 1 170 (by decide) (by decide)
      · right
        exact rec6605 1 170 (by decide) (by decide)
      · right
        exact rec6608 1 170 (by decide) (by decide)
      · right
        exact rec6611 1 170 (by decide) (by decide)
      · right
        exact rec6614 1 170 (by decide) (by decide)
      · right
        exact rec6617 1 170 (by decide) (by decide)
      · right
        exact rec6620 1 170 (by decide) (by decide)
      · right
        exact rec6623 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 128)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 129)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6626 1 170 (by decide) (by decide)
      · right
        exact rec6629 1 170 (by decide) (by decide)
      · right
        exact rec6632 1 170 (by decide) (by decide)
      · right
        exact rec6635 1 170 (by decide) (by decide)
      · right
        exact rec6638 1 170 (by decide) (by decide)
      · right
        exact rec6641 1 170 (by decide) (by decide)
      · right
        exact rec6644 1 170 (by decide) (by decide)
      · right
        exact rec6647 1 170 (by decide) (by decide)
      · right
        exact rec6650 1 170 (by decide) (by decide)
      · right
        exact rec6653 1 170 (by decide) (by decide)
      · right
        exact rec6656 1 170 (by decide) (by decide)
      · right
        exact rec6659 1 170 (by decide) (by decide)
      · right
        exact rec6662 1 170 (by decide) (by decide)
      · right
        exact rec6665 1 170 (by decide) (by decide)
      · right
        exact rec6668 1 170 (by decide) (by decide)
      · right
        exact rec6671 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 130)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 131)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 132)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6674 1 170 (by decide) (by decide)
      · right
        exact rec6677 1 170 (by decide) (by decide)
      · right
        exact rec6680 1 170 (by decide) (by decide)
      · right
        exact rec6683 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 133)).length = 20 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 134)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6686 1 170 (by decide) (by decide)
      · right
        exact rec6690 1 170 (by decide) (by decide)
      · right
        exact rec6693 1 170 (by decide) (by decide)
      · right
        exact rec6696 1 170 (by decide) (by decide)
      · right
        exact rec6699 1 170 (by decide) (by decide)
      · right
        exact rec6702 1 170 (by decide) (by decide)
      · right
        exact rec6705 1 170 (by decide) (by decide)
      · right
        exact rec6708 1 170 (by decide) (by decide)
      · right
        exact rec6711 1 170 (by decide) (by decide)
      · right
        exact rec6714 1 170 (by decide) (by decide)
      · right
        exact rec6717 1 170 (by decide) (by decide)
      · right
        exact rec6720 1 170 (by decide) (by decide)
      · right
        exact rec6723 1 170 (by decide) (by decide)
      · right
        exact rec6726 1 170 (by decide) (by decide)
      · right
        exact rec6729 1 170 (by decide) (by decide)
      · right
        exact rec6732 1 170 (by decide) (by decide)
      · right
        exact rec6735 1 170 (by decide) (by decide)
      · right
        exact rec6738 1 170 (by decide) (by decide)
      · right
        exact rec6741 1 170 (by decide) (by decide)
      · right
        exact rec6744 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 135)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6747 1 170 (by decide) (by decide)
      · right
        exact rec6750 1 170 (by decide) (by decide)
      · right
        exact rec6753 1 170 (by decide) (by decide)
      · right
        exact rec6756 1 170 (by decide) (by decide)
      · right
        exact rec6759 1 170 (by decide) (by decide)
      · right
        exact rec6762 1 170 (by decide) (by decide)
      · right
        exact rec6765 1 170 (by decide) (by decide)
      · right
        exact rec6768 1 170 (by decide) (by decide)
      · right
        exact rec6771 1 170 (by decide) (by decide)
      · right
        exact rec6774 1 170 (by decide) (by decide)
      · right
        exact rec6777 1 170 (by decide) (by decide)
      · right
        exact rec6780 1 170 (by decide) (by decide)
      · right
        exact rec6783 1 170 (by decide) (by decide)
      · right
        exact rec6786 1 170 (by decide) (by decide)
      · right
        exact rec6789 1 170 (by decide) (by decide)
      · right
        exact rec6792 1 170 (by decide) (by decide)
      · right
        exact rec6795 1 170 (by decide) (by decide)
      · right
        exact rec6798 1 170 (by decide) (by decide)
      · right
        exact rec6801 1 170 (by decide) (by decide)
      · right
        exact rec6806 1 170 (by decide) (by decide)
      · right
        exact rec6809 1 170 (by decide) (by decide)
      · right
        exact rec6812 1 170 (by decide) (by decide)
      · right
        exact rec6815 1 170 (by decide) (by decide)
      · right
        exact rec6818 1 170 (by decide) (by decide)
      · right
        exact rec6821 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 136)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6826 1 170 (by decide) (by decide)
      · right
        exact rec6830 1 170 (by decide) (by decide)
      · right
        exact rec6833 1 170 (by decide) (by decide)
      · right
        exact rec6836 1 170 (by decide) (by decide)
      · right
        exact rec6839 1 170 (by decide) (by decide)
      · right
        exact rec6842 1 170 (by decide) (by decide)
      · right
        exact rec6845 1 170 (by decide) (by decide)
      · right
        exact rec6849 1 170 (by decide) (by decide)
      · right
        exact rec6852 1 170 (by decide) (by decide)
      · right
        exact rec6855 1 170 (by decide) (by decide)
      · right
        exact rec6858 1 170 (by decide) (by decide)
      · right
        exact rec6861 1 170 (by decide) (by decide)
      · right
        exact rec6864 1 170 (by decide) (by decide)
      · right
        exact rec6867 1 170 (by decide) (by decide)
      · right
        exact rec6870 1 170 (by decide) (by decide)
      · right
        exact rec6873 1 170 (by decide) (by decide)
      · right
        exact rec6876 1 170 (by decide) (by decide)
      · right
        exact rec6879 1 170 (by decide) (by decide)
      · right
        exact rec6882 1 170 (by decide) (by decide)
      · right
        exact rec6885 1 170 (by decide) (by decide)
      · right
        exact rec6888 1 170 (by decide) (by decide)
      · right
        exact rec6891 1 170 (by decide) (by decide)
      · right
        exact rec6894 1 170 (by decide) (by decide)
      · right
        exact rec6897 1 170 (by decide) (by decide)
      · right
        exact rec6900 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 137)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 138)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6904 1 170 (by decide) (by decide)
      · right
        exact rec6907 1 170 (by decide) (by decide)
      · right
        exact rec6910 1 170 (by decide) (by decide)
      · right
        exact rec6913 1 170 (by decide) (by decide)
      · right
        exact rec6916 1 170 (by decide) (by decide)
      · right
        exact rec6919 1 170 (by decide) (by decide)
      · right
        exact rec6923 1 170 (by decide) (by decide)
      · right
        exact rec6927 1 170 (by decide) (by decide)
      · right
        exact rec6931 1 170 (by decide) (by decide)
      · right
        exact rec6935 1 170 (by decide) (by decide)
      · right
        exact rec6939 1 170 (by decide) (by decide)
      · right
        exact rec6942 1 170 (by decide) (by decide)
      · right
        exact rec6945 1 170 (by decide) (by decide)
      · right
        exact rec6948 1 170 (by decide) (by decide)
      · right
        exact rec6951 1 170 (by decide) (by decide)
      · right
        exact rec6954 1 170 (by decide) (by decide)
      · right
        exact rec6957 1 170 (by decide) (by decide)
      · right
        exact rec6960 1 170 (by decide) (by decide)
      · right
        exact rec6963 1 170 (by decide) (by decide)
      · right
        exact rec6966 1 170 (by decide) (by decide)
      · right
        exact rec6969 1 170 (by decide) (by decide)
      · right
        exact rec6972 1 170 (by decide) (by decide)
      · right
        exact rec6975 1 170 (by decide) (by decide)
      · right
        exact rec6978 1 170 (by decide) (by decide)
      · right
        exact rec6981 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 139)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6984 1 170 (by decide) (by decide)
      · right
        exact rec6987 1 170 (by decide) (by decide)
      · right
        exact rec6990 1 170 (by decide) (by decide)
      · right
        exact rec6993 1 170 (by decide) (by decide)
      · right
        exact rec6996 1 170 (by decide) (by decide)
      · right
        exact rec6999 1 170 (by decide) (by decide)
      · right
        exact rec7003 1 170 (by decide) (by decide)
      · right
        exact rec7007 1 170 (by decide) (by decide)
      · right
        exact rec7011 1 170 (by decide) (by decide)
      · right
        exact rec7014 1 170 (by decide) (by decide)
      · right
        exact rec7017 1 170 (by decide) (by decide)
      · right
        exact rec7020 1 170 (by decide) (by decide)
      · right
        exact rec7023 1 170 (by decide) (by decide)
      · right
        exact rec7026 1 170 (by decide) (by decide)
      · right
        exact rec7029 1 170 (by decide) (by decide)
      · right
        exact rec7032 1 170 (by decide) (by decide)
      · right
        exact rec7035 1 170 (by decide) (by decide)
      · right
        exact rec7038 1 170 (by decide) (by decide)
      · right
        exact rec7041 1 170 (by decide) (by decide)
      · right
        exact rec7044 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 140)).length = 8 := by decide +kernel
      have hjj : j < 8 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7047 1 170 (by decide) (by decide)
      · right
        exact rec7050 1 170 (by decide) (by decide)
      · right
        exact rec7053 1 170 (by decide) (by decide)
      · right
        exact rec7056 1 170 (by decide) (by decide)
      · right
        exact rec7061 1 170 (by decide) (by decide)
      · right
        exact rec7064 1 170 (by decide) (by decide)
      · right
        exact rec7067 1 170 (by decide) (by decide)
      · right
        exact rec7072 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 141)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 142)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7076 1 170 (by decide) (by decide)
      · right
        exact rec7079 1 170 (by decide) (by decide)
      · right
        exact rec7082 1 170 (by decide) (by decide)
      · right
        exact rec7085 1 170 (by decide) (by decide)
      · right
        exact rec7088 1 170 (by decide) (by decide)
      · right
        exact rec7091 1 170 (by decide) (by decide)
      · right
        exact rec7094 1 170 (by decide) (by decide)
      · right
        exact rec7097 1 170 (by decide) (by decide)
      · right
        exact rec7100 1 170 (by decide) (by decide)
      · right
        exact rec7103 1 170 (by decide) (by decide)
      · right
        exact rec7106 1 170 (by decide) (by decide)
      · right
        exact rec7109 1 170 (by decide) (by decide)
      · right
        exact rec7112 1 170 (by decide) (by decide)
      · right
        exact rec7115 1 170 (by decide) (by decide)
      · right
        exact rec7118 1 170 (by decide) (by decide)
      · right
        exact rec7121 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 143)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7124 1 170 (by decide) (by decide)
      · right
        exact rec7127 1 170 (by decide) (by decide)
      · right
        exact rec7130 1 170 (by decide) (by decide)
      · right
        exact rec7133 1 170 (by decide) (by decide)
      · right
        exact rec7136 1 170 (by decide) (by decide)
      · right
        exact rec7139 1 170 (by decide) (by decide)
      · right
        exact rec7142 1 170 (by decide) (by decide)
      · right
        exact rec7145 1 170 (by decide) (by decide)
      · right
        exact rec7148 1 170 (by decide) (by decide)
      · right
        exact rec7151 1 170 (by decide) (by decide)
      · right
        exact rec7154 1 170 (by decide) (by decide)
      · right
        exact rec7157 1 170 (by decide) (by decide)
      · right
        exact rec7160 1 170 (by decide) (by decide)
      · right
        exact rec7163 1 170 (by decide) (by decide)
      · right
        exact rec7166 1 170 (by decide) (by decide)
      · right
        exact rec7169 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 144)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7172 1 170 (by decide) (by decide)
      · right
        exact rec7175 1 170 (by decide) (by decide)
      · right
        exact rec7178 1 170 (by decide) (by decide)
      · right
        exact rec7181 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 145)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7184 1 170 (by decide) (by decide)
      · right
        exact rec7187 1 170 (by decide) (by decide)
      · right
        exact rec7191 1 170 (by decide) (by decide)
      · right
        exact rec7194 1 170 (by decide) (by decide)
      · right
        exact rec7198 1 170 (by decide) (by decide)
      · right
        exact rec7201 1 170 (by decide) (by decide)
      · right
        exact rec7204 1 170 (by decide) (by decide)
      · right
        exact rec7207 1 170 (by decide) (by decide)
      · right
        exact rec7210 1 170 (by decide) (by decide)
      · right
        exact rec7213 1 170 (by decide) (by decide)
      · right
        exact rec7216 1 170 (by decide) (by decide)
      · right
        exact rec7219 1 170 (by decide) (by decide)
      · right
        exact rec7222 1 170 (by decide) (by decide)
      · right
        exact rec7225 1 170 (by decide) (by decide)
      · right
        exact rec7228 1 170 (by decide) (by decide)
      · right
        exact rec7231 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 146)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7234 1 170 (by decide) (by decide)
      · right
        exact rec7238 1 170 (by decide) (by decide)
      · right
        exact rec7242 1 170 (by decide) (by decide)
      · right
        exact rec7245 1 170 (by decide) (by decide)
      · right
        exact rec7249 1 170 (by decide) (by decide)
      · right
        exact rec7252 1 170 (by decide) (by decide)
      · right
        exact rec7255 1 170 (by decide) (by decide)
      · right
        exact rec7258 1 170 (by decide) (by decide)
      · right
        exact rec7261 1 170 (by decide) (by decide)
      · right
        exact rec7264 1 170 (by decide) (by decide)
      · right
        exact rec7267 1 170 (by decide) (by decide)
      · right
        exact rec7270 1 170 (by decide) (by decide)
      · right
        exact rec7273 1 170 (by decide) (by decide)
      · right
        exact rec7276 1 170 (by decide) (by decide)
      · right
        exact rec7279 1 170 (by decide) (by decide)
      · right
        exact rec7282 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 147)).length = 20 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 148)).length = 20 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 149)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 150)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7285 1 170 (by decide) (by decide)
      · right
        exact rec7288 1 170 (by decide) (by decide)
      · right
        exact rec7291 1 170 (by decide) (by decide)
      · right
        exact rec7294 1 170 (by decide) (by decide)
      · right
        exact rec7297 1 170 (by decide) (by decide)
      · right
        exact rec7300 1 170 (by decide) (by decide)
      · right
        exact rec7303 1 170 (by decide) (by decide)
      · right
        exact rec7306 1 170 (by decide) (by decide)
      · right
        exact rec7309 1 170 (by decide) (by decide)
      · right
        exact rec7312 1 170 (by decide) (by decide)
      · right
        exact rec7315 1 170 (by decide) (by decide)
      · right
        exact rec7318 1 170 (by decide) (by decide)
      · right
        exact rec7321 1 170 (by decide) (by decide)
      · right
        exact rec7324 1 170 (by decide) (by decide)
      · right
        exact rec7327 1 170 (by decide) (by decide)
      · right
        exact rec7330 1 170 (by decide) (by decide)
      · right
        exact rec7333 1 170 (by decide) (by decide)
      · right
        exact rec7336 1 170 (by decide) (by decide)
      · right
        exact rec7339 1 170 (by decide) (by decide)
      · right
        exact rec7342 1 170 (by decide) (by decide)
      · right
        exact rec7345 1 170 (by decide) (by decide)
      · right
        exact rec7348 1 170 (by decide) (by decide)
      · right
        exact rec7351 1 170 (by decide) (by decide)
      · right
        exact rec7354 1 170 (by decide) (by decide)
      · right
        exact rec7357 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 151)).length = 20 := by decide +kernel
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
        exact rec7360 1 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec7362 1 170 (by decide) (by decide)
      · right
        exact rec7363 1 170 (by decide) (by decide)
      · right
        exact rec7364 1 170 (by decide) (by decide)
      · left
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
        exact rec7366 1 170 (by decide) (by decide)
      · right
        exact rec7368 1 170 (by decide) (by decide)
      · right
        exact rec7369 1 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec7370 1 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 152)).length = 10 := by decide +kernel
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
    exact rec5563 1 171 (by decide) (by decide)
  · left
    exact rec5556 1 172 (by decide) (by decide)
  · left
    exact rec5556 1 173 (by decide) (by decide)
  · left
    exact rec5565 1 174 (by decide) (by decide)
  · left
    exact rec5563 1 175 (by decide) (by decide)
end Section14Coverage_1_4_p168_176

#print axioms solution
