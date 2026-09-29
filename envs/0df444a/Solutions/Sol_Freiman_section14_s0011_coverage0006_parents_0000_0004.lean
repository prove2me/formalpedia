-- Prove2me | solution 1 for Freiman.section14_s0011_coverage0006_parents_0000_0004
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T12:13:28.333876+00:00
-- url     : https://prove2.me/submissions/f2aee8c8-b941-4d40-a459-c93637428ecc

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
namespace Section14Coverage_11_6_p0_4
private theorem rec15178 (si parent : ℕ) (hs : si ∈ ([3, 7, 11, 15] : List ℕ)) (hp : parent ∈ ([0] : List ℕ)) : section14Recorded section14Catalog si parent 413 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨413,(-1),[3,7,11,15],[0],881⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[257]? = some (⟨413,(-1),[3,7,11,15],[0],881⟩) from rfl))
private theorem rec15185 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 413 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨413,(-1),[11],[1],883⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[264]? = some (⟨413,(-1),[11],[1],883⟩) from rfl))
private theorem rec15186 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 413 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨413,(-1),[11],[3],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[265]? = some (⟨413,(-1),[11],[3],910⟩) from rfl))
private theorem rec15188 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 415 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(0),[11],[2],1697⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[267]? = some (⟨415,(0),[11],[2],1697⟩) from rfl))
private theorem rec15190 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 415 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(1),[11],[2],1697⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[269]? = some (⟨415,(1),[11],[2],1697⟩) from rfl))
private theorem rec15192 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 415 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(2),[11],[2],1698⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[271]? = some (⟨415,(2),[11],[2],1698⟩) from rfl))
private theorem rec15194 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 415 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(3),[11],[2],1698⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[273]? = some (⟨415,(3),[11],[2],1698⟩) from rfl))
private theorem rec15196 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 415 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(4),[11],[2],1699⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[275]? = some (⟨415,(4),[11],[2],1699⟩) from rfl))
private theorem rec15198 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 415 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(5),[11],[2],1700⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[277]? = some (⟨415,(5),[11],[2],1700⟩) from rfl))
private theorem rec15200 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 415 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(6),[11],[2],1699⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[279]? = some (⟨415,(6),[11],[2],1699⟩) from rfl))
private theorem rec15202 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 415 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(7),[11],[2],1701⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[281]? = some (⟨415,(7),[11],[2],1701⟩) from rfl))
private theorem rec15204 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 415 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(8),[11],[2],1699⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[283]? = some (⟨415,(8),[11],[2],1699⟩) from rfl))
private theorem rec15206 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 415 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(9),[11],[2],1700⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[285]? = some (⟨415,(9),[11],[2],1700⟩) from rfl))
private theorem rec15233 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(0),[11],[2],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[312]? = some (⟨420,(0),[11],[2],1086⟩) from rfl))
private theorem rec15235 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(1),[11],[2],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[314]? = some (⟨420,(1),[11],[2],1087⟩) from rfl))
private theorem rec15237 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(2),[11],[2],1088⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[316]? = some (⟨420,(2),[11],[2],1088⟩) from rfl))
private theorem rec15239 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(3),[11],[2],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[318]? = some (⟨420,(3),[11],[2],1089⟩) from rfl))
private theorem rec15241 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(4),[11],[2],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[320]? = some (⟨420,(4),[11],[2],1086⟩) from rfl))
private theorem rec15243 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(5),[11],[2],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[322]? = some (⟨420,(5),[11],[2],1087⟩) from rfl))
private theorem rec15245 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(6),[11],[2],1090⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[324]? = some (⟨420,(6),[11],[2],1090⟩) from rfl))
private theorem rec15247 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(7),[11],[2],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[326]? = some (⟨420,(7),[11],[2],1089⟩) from rfl))
private theorem rec15249 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(8),[11],[2],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[328]? = some (⟨420,(8),[11],[2],1086⟩) from rfl))
private theorem rec15251 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(9),[11],[2],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[330]? = some (⟨420,(9),[11],[2],1087⟩) from rfl))
private theorem rec15253 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(10),[11],[2],1088⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[332]? = some (⟨420,(10),[11],[2],1088⟩) from rfl))
private theorem rec15255 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(11),[11],[2],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[334]? = some (⟨420,(11),[11],[2],1089⟩) from rfl))
private theorem rec15257 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(12),[11],[2],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[336]? = some (⟨420,(12),[11],[2],1086⟩) from rfl))
private theorem rec15259 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(13),[11],[2],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[338]? = some (⟨420,(13),[11],[2],1087⟩) from rfl))
private theorem rec15261 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(14),[11],[2],1091⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[340]? = some (⟨420,(14),[11],[2],1091⟩) from rfl))
private theorem rec15263 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 420 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(15),[11],[2],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[342]? = some (⟨420,(15),[11],[2],1089⟩) from rfl))
private theorem rec15265 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(0),[11],[2],1092⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[344]? = some (⟨423,(0),[11],[2],1092⟩) from rfl))
private theorem rec15267 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(1),[11],[2],1093⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[346]? = some (⟨423,(1),[11],[2],1093⟩) from rfl))
private theorem rec15269 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(2),[11],[2],1092⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[348]? = some (⟨423,(2),[11],[2],1092⟩) from rfl))
private theorem rec15271 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(3),[11],[2],1094⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[350]? = some (⟨423,(3),[11],[2],1094⟩) from rfl))
private theorem rec15273 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(4),[11],[2],1095⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[352]? = some (⟨423,(4),[11],[2],1095⟩) from rfl))
private theorem rec15275 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(5),[11],[2],1095⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[354]? = some (⟨423,(5),[11],[2],1095⟩) from rfl))
private theorem rec15277 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(6),[11],[2],1095⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[356]? = some (⟨423,(6),[11],[2],1095⟩) from rfl))
private theorem rec15279 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(7),[11],[2],1095⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[358]? = some (⟨423,(7),[11],[2],1095⟩) from rfl))
private theorem rec15281 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(8),[11],[2],1096⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[360]? = some (⟨423,(8),[11],[2],1096⟩) from rfl))
private theorem rec15283 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(9),[11],[2],1096⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[362]? = some (⟨423,(9),[11],[2],1096⟩) from rfl))
private theorem rec15285 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(10),[11],[2],1096⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[364]? = some (⟨423,(10),[11],[2],1096⟩) from rfl))
private theorem rec15287 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(11),[11],[2],1096⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[366]? = some (⟨423,(11),[11],[2],1096⟩) from rfl))
private theorem rec15289 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(12),[11],[2],1097⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[368]? = some (⟨423,(12),[11],[2],1097⟩) from rfl))
private theorem rec15291 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(13),[11],[2],1097⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[370]? = some (⟨423,(13),[11],[2],1097⟩) from rfl))
private theorem rec15293 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(14),[11],[2],1097⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[372]? = some (⟨423,(14),[11],[2],1097⟩) from rfl))
private theorem rec15295 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 423 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(15),[11],[2],1097⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[374]? = some (⟨423,(15),[11],[2],1097⟩) from rfl))
private theorem rec15297 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 426 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(0),[11],[2],1098⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[376]? = some (⟨426,(0),[11],[2],1098⟩) from rfl))
private theorem rec15299 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 426 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(1),[11],[2],1099⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[378]? = some (⟨426,(1),[11],[2],1099⟩) from rfl))
private theorem rec15301 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 426 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(2),[11],[2],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[380]? = some (⟨426,(2),[11],[2],1100⟩) from rfl))
private theorem rec15303 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 426 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(3),[11],[2],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[382]? = some (⟨426,(3),[11],[2],1100⟩) from rfl))
private theorem rec15305 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 426 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(4),[11],[2],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[384]? = some (⟨426,(4),[11],[2],1100⟩) from rfl))
private theorem rec15307 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 426 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(5),[11],[2],1098⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[386]? = some (⟨426,(5),[11],[2],1098⟩) from rfl))
private theorem rec15309 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 426 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(6),[11],[2],1099⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[388]? = some (⟨426,(6),[11],[2],1099⟩) from rfl))
private theorem rec15311 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 426 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(7),[11],[2],1101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[390]? = some (⟨426,(7),[11],[2],1101⟩) from rfl))
private theorem rec15313 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 426 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(8),[11],[2],1102⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[392]? = some (⟨426,(8),[11],[2],1102⟩) from rfl))
private theorem rec15315 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 426 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(9),[11],[2],1101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[394]? = some (⟨426,(9),[11],[2],1101⟩) from rfl))
private theorem rec15317 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 428 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(0),[11],[2],1103⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[396]? = some (⟨428,(0),[11],[2],1103⟩) from rfl))
private theorem rec15319 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 428 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(1),[11],[2],1103⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[398]? = some (⟨428,(1),[11],[2],1103⟩) from rfl))
private theorem rec15321 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 428 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(2),[11],[2],1104⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[400]? = some (⟨428,(2),[11],[2],1104⟩) from rfl))
private theorem rec15323 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 428 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(3),[11],[2],1105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[402]? = some (⟨428,(3),[11],[2],1105⟩) from rfl))
private theorem rec15325 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 428 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(4),[11],[2],1106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[404]? = some (⟨428,(4),[11],[2],1106⟩) from rfl))
private theorem rec15327 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 428 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(5),[11],[2],1107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[406]? = some (⟨428,(5),[11],[2],1107⟩) from rfl))
private theorem rec15329 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 428 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(6),[11],[2],1107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[408]? = some (⟨428,(6),[11],[2],1107⟩) from rfl))
private theorem rec15331 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 428 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(7),[11],[2],1107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[410]? = some (⟨428,(7),[11],[2],1107⟩) from rfl))
private theorem rec15333 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 428 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(8),[11],[2],1105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[412]? = some (⟨428,(8),[11],[2],1105⟩) from rfl))
private theorem rec15335 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 428 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(9),[11],[2],1106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[414]? = some (⟨428,(9),[11],[2],1106⟩) from rfl))
private theorem rec15337 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(0),[11],[2],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[416]? = some (⟨431,(0),[11],[2],1108⟩) from rfl))
private theorem rec15339 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(1),[11],[2],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[418]? = some (⟨431,(1),[11],[2],1109⟩) from rfl))
private theorem rec15341 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(2),[11],[2],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[420]? = some (⟨431,(2),[11],[2],1110⟩) from rfl))
private theorem rec15343 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(3),[11],[2],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[422]? = some (⟨431,(3),[11],[2],1110⟩) from rfl))
private theorem rec15345 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(4),[11],[2],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[424]? = some (⟨431,(4),[11],[2],1110⟩) from rfl))
private theorem rec15347 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(5),[11],[2],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[426]? = some (⟨431,(5),[11],[2],1108⟩) from rfl))
private theorem rec15349 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(6),[11],[2],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[428]? = some (⟨431,(6),[11],[2],1109⟩) from rfl))
private theorem rec15351 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(7),[11],[2],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[430]? = some (⟨431,(7),[11],[2],1111⟩) from rfl))
private theorem rec15353 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(8),[11],[2],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[432]? = some (⟨431,(8),[11],[2],1112⟩) from rfl))
private theorem rec15355 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(9),[11],[2],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[434]? = some (⟨431,(9),[11],[2],1111⟩) from rfl))
private theorem rec15357 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(10),[11],[2],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[436]? = some (⟨431,(10),[11],[2],1108⟩) from rfl))
private theorem rec15359 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(11),[11],[2],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[438]? = some (⟨431,(11),[11],[2],1109⟩) from rfl))
private theorem rec15361 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(12),[11],[2],1113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[440]? = some (⟨431,(12),[11],[2],1113⟩) from rfl))
private theorem rec15363 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(13),[11],[2],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[442]? = some (⟨431,(13),[11],[2],1112⟩) from rfl))
private theorem rec15365 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(14),[11],[2],1113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[444]? = some (⟨431,(14),[11],[2],1113⟩) from rfl))
private theorem rec15367 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(15),[11],[2],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[446]? = some (⟨431,(15),[11],[2],1108⟩) from rfl))
private theorem rec15369 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(16),[11],[2],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[448]? = some (⟨431,(16),[11],[2],1109⟩) from rfl))
private theorem rec15371 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(17),[11],[2],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[450]? = some (⟨431,(17),[11],[2],1111⟩) from rfl))
private theorem rec15373 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(18),[11],[2],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[452]? = some (⟨431,(18),[11],[2],1112⟩) from rfl))
private theorem rec15375 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(19),[11],[2],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[454]? = some (⟨431,(19),[11],[2],1111⟩) from rfl))
private theorem rec15377 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(20),[11],[2],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[456]? = some (⟨431,(20),[11],[2],1108⟩) from rfl))
private theorem rec15379 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(21),[11],[2],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[458]? = some (⟨431,(21),[11],[2],1109⟩) from rfl))
private theorem rec15381 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(22),[11],[2],1114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[460]? = some (⟨431,(22),[11],[2],1114⟩) from rfl))
private theorem rec15383 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(23),[11],[2],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[462]? = some (⟨431,(23),[11],[2],1112⟩) from rfl))
private theorem rec15385 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 431 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(24),[11],[2],1114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[464]? = some (⟨431,(24),[11],[2],1114⟩) from rfl))
private theorem rec15387 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 433 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(0),[11],[2],1115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[466]? = some (⟨433,(0),[11],[2],1115⟩) from rfl))
private theorem rec15389 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 433 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(1),[11],[2],1115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[468]? = some (⟨433,(1),[11],[2],1115⟩) from rfl))
private theorem rec15391 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 433 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(2),[11],[2],1116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[470]? = some (⟨433,(2),[11],[2],1116⟩) from rfl))
private theorem rec15393 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 433 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(3),[11],[2],1117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[472]? = some (⟨433,(3),[11],[2],1117⟩) from rfl))
private theorem rec15395 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 433 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(4),[11],[2],1118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[474]? = some (⟨433,(4),[11],[2],1118⟩) from rfl))
private theorem rec15397 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 433 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(5),[11],[2],1119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[476]? = some (⟨433,(5),[11],[2],1119⟩) from rfl))
private theorem rec15399 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 433 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(6),[11],[2],1119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[478]? = some (⟨433,(6),[11],[2],1119⟩) from rfl))
private theorem rec15401 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 433 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(7),[11],[2],1119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[480]? = some (⟨433,(7),[11],[2],1119⟩) from rfl))
private theorem rec15403 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 433 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(8),[11],[2],1117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[482]? = some (⟨433,(8),[11],[2],1117⟩) from rfl))
private theorem rec15405 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 433 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(9),[11],[2],1118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[484]? = some (⟨433,(9),[11],[2],1118⟩) from rfl))
private theorem rec15407 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 436 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(0),[11],[2],1120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[486]? = some (⟨436,(0),[11],[2],1120⟩) from rfl))
private theorem rec15409 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 436 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(1),[11],[2],1121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[488]? = some (⟨436,(1),[11],[2],1121⟩) from rfl))
private theorem rec15411 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 436 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(2),[11],[2],1122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[490]? = some (⟨436,(2),[11],[2],1122⟩) from rfl))
private theorem rec15413 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 436 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(3),[11],[2],1122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[492]? = some (⟨436,(3),[11],[2],1122⟩) from rfl))
private theorem rec15415 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 436 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(4),[11],[2],1123⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[494]? = some (⟨436,(4),[11],[2],1123⟩) from rfl))
private theorem rec15417 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 436 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(5),[11],[2],1120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[496]? = some (⟨436,(5),[11],[2],1120⟩) from rfl))
private theorem rec15419 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 436 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(6),[11],[2],1121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[498]? = some (⟨436,(6),[11],[2],1121⟩) from rfl))
private theorem rec15421 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 436 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(7),[11],[2],1124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[500]? = some (⟨436,(7),[11],[2],1124⟩) from rfl))
private theorem rec15423 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 436 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(8),[11],[2],1125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[502]? = some (⟨436,(8),[11],[2],1125⟩) from rfl))
private theorem rec15425 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 436 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(9),[11],[2],1126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[504]? = some (⟨436,(9),[11],[2],1126⟩) from rfl))
private theorem rec15427 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(0),[11],[2],1127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[506]? = some (⟨438,(0),[11],[2],1127⟩) from rfl))
private theorem rec15429 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(1),[11],[2],1127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[508]? = some (⟨438,(1),[11],[2],1127⟩) from rfl))
private theorem rec15431 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(2),[11],[2],1128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[510]? = some (⟨438,(2),[11],[2],1128⟩) from rfl))
private theorem rec15433 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(3),[11],[2],1129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[512]? = some (⟨438,(3),[11],[2],1129⟩) from rfl))
private theorem rec15435 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(4),[11],[2],1130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[514]? = some (⟨438,(4),[11],[2],1130⟩) from rfl))
private theorem rec15437 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(5),[11],[2],1131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[516]? = some (⟨438,(5),[11],[2],1131⟩) from rfl))
private theorem rec15439 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(6),[11],[2],1131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[518]? = some (⟨438,(6),[11],[2],1131⟩) from rfl))
private theorem rec15441 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(7),[11],[2],1128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[520]? = some (⟨438,(7),[11],[2],1128⟩) from rfl))
private theorem rec15443 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(8),[11],[2],1129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[522]? = some (⟨438,(8),[11],[2],1129⟩) from rfl))
private theorem rec15445 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(9),[11],[2],1130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[524]? = some (⟨438,(9),[11],[2],1130⟩) from rfl))
private theorem rec15447 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(10),[11],[2],1127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[526]? = some (⟨438,(10),[11],[2],1127⟩) from rfl))
private theorem rec15449 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(11),[11],[2],1127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[528]? = some (⟨438,(11),[11],[2],1127⟩) from rfl))
private theorem rec15451 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(12),[11],[2],1128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[530]? = some (⟨438,(12),[11],[2],1128⟩) from rfl))
private theorem rec15453 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(13),[11],[2],1129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[532]? = some (⟨438,(13),[11],[2],1129⟩) from rfl))
private theorem rec15455 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(14),[11],[2],1130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[534]? = some (⟨438,(14),[11],[2],1130⟩) from rfl))
private theorem rec15457 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(15),[11],[2],1132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[536]? = some (⟨438,(15),[11],[2],1132⟩) from rfl))
private theorem rec15459 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(16),[11],[2],1132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[538]? = some (⟨438,(16),[11],[2],1132⟩) from rfl))
private theorem rec15461 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(17),[11],[2],1128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[540]? = some (⟨438,(17),[11],[2],1128⟩) from rfl))
private theorem rec15463 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(18),[11],[2],1129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[542]? = some (⟨438,(18),[11],[2],1129⟩) from rfl))
private theorem rec15465 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(19),[11],[2],1130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[544]? = some (⟨438,(19),[11],[2],1130⟩) from rfl))
private theorem rec15467 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(20),[11],[2],1133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[546]? = some (⟨438,(20),[11],[2],1133⟩) from rfl))
private theorem rec15469 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(21),[11],[2],1133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[548]? = some (⟨438,(21),[11],[2],1133⟩) from rfl))
private theorem rec15471 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(22),[11],[2],1133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[550]? = some (⟨438,(22),[11],[2],1133⟩) from rfl))
private theorem rec15473 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(23),[11],[2],1129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[552]? = some (⟨438,(23),[11],[2],1129⟩) from rfl))
private theorem rec15475 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 438 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(24),[11],[2],1130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[554]? = some (⟨438,(24),[11],[2],1130⟩) from rfl))
private theorem rec15477 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(0),[11],[2],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[556]? = some (⟨441,(0),[11],[2],1134⟩) from rfl))
private theorem rec15479 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(1),[11],[2],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[558]? = some (⟨441,(1),[11],[2],1135⟩) from rfl))
private theorem rec15481 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(2),[11],[2],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[560]? = some (⟨441,(2),[11],[2],1136⟩) from rfl))
private theorem rec15483 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(3),[11],[2],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[562]? = some (⟨441,(3),[11],[2],1136⟩) from rfl))
private theorem rec15485 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(4),[11],[2],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[564]? = some (⟨441,(4),[11],[2],1136⟩) from rfl))
private theorem rec15487 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(5),[11],[2],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[566]? = some (⟨441,(5),[11],[2],1134⟩) from rfl))
private theorem rec15489 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(6),[11],[2],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[568]? = some (⟨441,(6),[11],[2],1135⟩) from rfl))
private theorem rec15491 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(7),[11],[2],1137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[570]? = some (⟨441,(7),[11],[2],1137⟩) from rfl))
private theorem rec15493 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(8),[11],[2],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[572]? = some (⟨441,(8),[11],[2],1138⟩) from rfl))
private theorem rec15495 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(9),[11],[2],1137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[574]? = some (⟨441,(9),[11],[2],1137⟩) from rfl))
private theorem rec15497 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(10),[11],[2],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[576]? = some (⟨441,(10),[11],[2],1134⟩) from rfl))
private theorem rec15499 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(11),[11],[2],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[578]? = some (⟨441,(11),[11],[2],1135⟩) from rfl))
private theorem rec15501 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(12),[11],[2],1139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[580]? = some (⟨441,(12),[11],[2],1139⟩) from rfl))
private theorem rec15503 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(13),[11],[2],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[582]? = some (⟨441,(13),[11],[2],1138⟩) from rfl))
private theorem rec15505 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(14),[11],[2],1139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[584]? = some (⟨441,(14),[11],[2],1139⟩) from rfl))
private theorem rec15507 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(15),[11],[2],1140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[586]? = some (⟨441,(15),[11],[2],1140⟩) from rfl))
private theorem rec15509 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(16),[11],[2],1141⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[588]? = some (⟨441,(16),[11],[2],1141⟩) from rfl))
private theorem rec15511 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(17),[11],[2],1142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[590]? = some (⟨441,(17),[11],[2],1142⟩) from rfl))
private theorem rec15513 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(18),[11],[2],1143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[592]? = some (⟨441,(18),[11],[2],1143⟩) from rfl))
private theorem rec15515 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(19),[11],[2],1142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[594]? = some (⟨441,(19),[11],[2],1142⟩) from rfl))
private theorem rec15517 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(20),[11],[2],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[596]? = some (⟨441,(20),[11],[2],1134⟩) from rfl))
private theorem rec15519 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(21),[11],[2],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[598]? = some (⟨441,(21),[11],[2],1135⟩) from rfl))
private theorem rec15521 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(22),[11],[2],1144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[600]? = some (⟨441,(22),[11],[2],1144⟩) from rfl))
private theorem rec15523 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(23),[11],[2],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[602]? = some (⟨441,(23),[11],[2],1138⟩) from rfl))
private theorem rec15525 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 441 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(24),[11],[2],1144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[604]? = some (⟨441,(24),[11],[2],1144⟩) from rfl))
private theorem rec15527 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(0),[11],[2],1145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[606]? = some (⟨443,(0),[11],[2],1145⟩) from rfl))
private theorem rec15529 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(1),[11],[2],1145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[608]? = some (⟨443,(1),[11],[2],1145⟩) from rfl))
private theorem rec15531 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(2),[11],[2],1146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[610]? = some (⟨443,(2),[11],[2],1146⟩) from rfl))
private theorem rec15533 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(3),[11],[2],1147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[612]? = some (⟨443,(3),[11],[2],1147⟩) from rfl))
private theorem rec15535 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(4),[11],[2],1148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[614]? = some (⟨443,(4),[11],[2],1148⟩) from rfl))
private theorem rec15537 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(5),[11],[2],1149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[616]? = some (⟨443,(5),[11],[2],1149⟩) from rfl))
private theorem rec15539 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(6),[11],[2],1149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[618]? = some (⟨443,(6),[11],[2],1149⟩) from rfl))
private theorem rec15541 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(7),[11],[2],1146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[620]? = some (⟨443,(7),[11],[2],1146⟩) from rfl))
private theorem rec15543 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(8),[11],[2],1147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[622]? = some (⟨443,(8),[11],[2],1147⟩) from rfl))
private theorem rec15545 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(9),[11],[2],1148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[624]? = some (⟨443,(9),[11],[2],1148⟩) from rfl))
private theorem rec15547 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(10),[11],[2],1145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[626]? = some (⟨443,(10),[11],[2],1145⟩) from rfl))
private theorem rec15549 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(11),[11],[2],1145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[628]? = some (⟨443,(11),[11],[2],1145⟩) from rfl))
private theorem rec15551 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(12),[11],[2],1146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[630]? = some (⟨443,(12),[11],[2],1146⟩) from rfl))
private theorem rec15553 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(13),[11],[2],1147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[632]? = some (⟨443,(13),[11],[2],1147⟩) from rfl))
private theorem rec15555 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(14),[11],[2],1148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[634]? = some (⟨443,(14),[11],[2],1148⟩) from rfl))
private theorem rec15557 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(15),[11],[2],1150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[636]? = some (⟨443,(15),[11],[2],1150⟩) from rfl))
private theorem rec15559 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(16),[11],[2],1150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[638]? = some (⟨443,(16),[11],[2],1150⟩) from rfl))
private theorem rec15561 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(17),[11],[2],1146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[640]? = some (⟨443,(17),[11],[2],1146⟩) from rfl))
private theorem rec15563 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(18),[11],[2],1147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[642]? = some (⟨443,(18),[11],[2],1147⟩) from rfl))
private theorem rec15565 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(19),[11],[2],1148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[644]? = some (⟨443,(19),[11],[2],1148⟩) from rfl))
private theorem rec15567 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(20),[11],[2],1151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[646]? = some (⟨443,(20),[11],[2],1151⟩) from rfl))
private theorem rec15569 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(21),[11],[2],1151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[648]? = some (⟨443,(21),[11],[2],1151⟩) from rfl))
private theorem rec15571 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(22),[11],[2],1151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[650]? = some (⟨443,(22),[11],[2],1151⟩) from rfl))
private theorem rec15573 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(23),[11],[2],1147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[652]? = some (⟨443,(23),[11],[2],1147⟩) from rfl))
private theorem rec15575 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 443 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(24),[11],[2],1148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[654]? = some (⟨443,(24),[11],[2],1148⟩) from rfl))
private theorem rec15577 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(0),[11],[2],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[656]? = some (⟨446,(0),[11],[2],1152⟩) from rfl))
private theorem rec15579 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(1),[11],[2],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[658]? = some (⟨446,(1),[11],[2],1153⟩) from rfl))
private theorem rec15581 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(2),[11],[2],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[660]? = some (⟨446,(2),[11],[2],1154⟩) from rfl))
private theorem rec15583 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(3),[11],[2],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[662]? = some (⟨446,(3),[11],[2],1154⟩) from rfl))
private theorem rec15585 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(4),[11],[2],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[664]? = some (⟨446,(4),[11],[2],1154⟩) from rfl))
private theorem rec15587 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(5),[11],[2],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[666]? = some (⟨446,(5),[11],[2],1152⟩) from rfl))
private theorem rec15589 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(6),[11],[2],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[668]? = some (⟨446,(6),[11],[2],1153⟩) from rfl))
private theorem rec15591 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(7),[11],[2],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[670]? = some (⟨446,(7),[11],[2],1155⟩) from rfl))
private theorem rec15593 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(8),[11],[2],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[672]? = some (⟨446,(8),[11],[2],1156⟩) from rfl))
private theorem rec15595 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(9),[11],[2],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[674]? = some (⟨446,(9),[11],[2],1155⟩) from rfl))
private theorem rec15597 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(10),[11],[2],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[676]? = some (⟨446,(10),[11],[2],1152⟩) from rfl))
private theorem rec15599 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(11),[11],[2],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[678]? = some (⟨446,(11),[11],[2],1153⟩) from rfl))
private theorem rec15601 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(12),[11],[2],1157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[680]? = some (⟨446,(12),[11],[2],1157⟩) from rfl))
private theorem rec15603 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(13),[11],[2],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[682]? = some (⟨446,(13),[11],[2],1156⟩) from rfl))
private theorem rec15605 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(14),[11],[2],1157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[684]? = some (⟨446,(14),[11],[2],1157⟩) from rfl))
private theorem rec15607 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(15),[11],[2],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[686]? = some (⟨446,(15),[11],[2],1152⟩) from rfl))
private theorem rec15609 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(16),[11],[2],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[688]? = some (⟨446,(16),[11],[2],1153⟩) from rfl))
private theorem rec15611 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(17),[11],[2],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[690]? = some (⟨446,(17),[11],[2],1155⟩) from rfl))
private theorem rec15613 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(18),[11],[2],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[692]? = some (⟨446,(18),[11],[2],1156⟩) from rfl))
private theorem rec15615 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(19),[11],[2],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[694]? = some (⟨446,(19),[11],[2],1155⟩) from rfl))
private theorem rec15617 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(20),[11],[2],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[696]? = some (⟨446,(20),[11],[2],1152⟩) from rfl))
private theorem rec15619 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(21),[11],[2],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[698]? = some (⟨446,(21),[11],[2],1153⟩) from rfl))
private theorem rec15621 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(22),[11],[2],1158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[700]? = some (⟨446,(22),[11],[2],1158⟩) from rfl))
private theorem rec15623 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(23),[11],[2],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[702]? = some (⟨446,(23),[11],[2],1156⟩) from rfl))
private theorem rec15625 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 446 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(24),[11],[2],1158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[704]? = some (⟨446,(24),[11],[2],1158⟩) from rfl))
private theorem rec15627 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(0),[11],[2],1159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[706]? = some (⟨448,(0),[11],[2],1159⟩) from rfl))
private theorem rec15629 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(1),[11],[2],1159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[708]? = some (⟨448,(1),[11],[2],1159⟩) from rfl))
private theorem rec15631 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(2),[11],[2],1160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[710]? = some (⟨448,(2),[11],[2],1160⟩) from rfl))
private theorem rec15633 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(3),[11],[2],1161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[712]? = some (⟨448,(3),[11],[2],1161⟩) from rfl))
private theorem rec15635 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(4),[11],[2],1162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[714]? = some (⟨448,(4),[11],[2],1162⟩) from rfl))
private theorem rec15637 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(5),[11],[2],1163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[716]? = some (⟨448,(5),[11],[2],1163⟩) from rfl))
private theorem rec15639 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(6),[11],[2],1163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[718]? = some (⟨448,(6),[11],[2],1163⟩) from rfl))
private theorem rec15641 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(7),[11],[2],1160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[720]? = some (⟨448,(7),[11],[2],1160⟩) from rfl))
private theorem rec15643 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(8),[11],[2],1161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[722]? = some (⟨448,(8),[11],[2],1161⟩) from rfl))
private theorem rec15645 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(9),[11],[2],1162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[724]? = some (⟨448,(9),[11],[2],1162⟩) from rfl))
private theorem rec15647 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(10),[11],[2],1159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[726]? = some (⟨448,(10),[11],[2],1159⟩) from rfl))
private theorem rec15649 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(11),[11],[2],1159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[728]? = some (⟨448,(11),[11],[2],1159⟩) from rfl))
private theorem rec15651 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(12),[11],[2],1160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[730]? = some (⟨448,(12),[11],[2],1160⟩) from rfl))
private theorem rec15653 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(13),[11],[2],1161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[732]? = some (⟨448,(13),[11],[2],1161⟩) from rfl))
private theorem rec15655 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(14),[11],[2],1162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[734]? = some (⟨448,(14),[11],[2],1162⟩) from rfl))
private theorem rec15657 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(15),[11],[2],1164⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[736]? = some (⟨448,(15),[11],[2],1164⟩) from rfl))
private theorem rec15659 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(16),[11],[2],1164⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[738]? = some (⟨448,(16),[11],[2],1164⟩) from rfl))
private theorem rec15661 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(17),[11],[2],1160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[740]? = some (⟨448,(17),[11],[2],1160⟩) from rfl))
private theorem rec15663 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(18),[11],[2],1161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[742]? = some (⟨448,(18),[11],[2],1161⟩) from rfl))
private theorem rec15665 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(19),[11],[2],1162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[744]? = some (⟨448,(19),[11],[2],1162⟩) from rfl))
private theorem rec15667 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(20),[11],[2],1165⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[746]? = some (⟨448,(20),[11],[2],1165⟩) from rfl))
private theorem rec15669 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(21),[11],[2],1165⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[748]? = some (⟨448,(21),[11],[2],1165⟩) from rfl))
private theorem rec15671 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(22),[11],[2],1165⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[750]? = some (⟨448,(22),[11],[2],1165⟩) from rfl))
private theorem rec15673 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(23),[11],[2],1161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[752]? = some (⟨448,(23),[11],[2],1161⟩) from rfl))
private theorem rec15675 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 448 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(24),[11],[2],1162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[754]? = some (⟨448,(24),[11],[2],1162⟩) from rfl))
private theorem rec15677 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 450 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨450,(0),[11],[2],1166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[756]? = some (⟨450,(0),[11],[2],1166⟩) from rfl))
private theorem rec15679 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 450 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨450,(1),[11],[2],1167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[758]? = some (⟨450,(1),[11],[2],1167⟩) from rfl))
private theorem rec15681 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 450 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨450,(2),[11],[2],1168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[760]? = some (⟨450,(2),[11],[2],1168⟩) from rfl))
private theorem rec15683 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 450 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨450,(3),[11],[2],1169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[762]? = some (⟨450,(3),[11],[2],1169⟩) from rfl))
private theorem rec15685 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(0),[11],[2],1170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[764]? = some (⟨453,(0),[11],[2],1170⟩) from rfl))
private theorem rec15687 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(1),[11],[2],1171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[766]? = some (⟨453,(1),[11],[2],1171⟩) from rfl))
private theorem rec15689 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(2),[11],[2],1170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[768]? = some (⟨453,(2),[11],[2],1170⟩) from rfl))
private theorem rec15691 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(3),[11],[2],1172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[770]? = some (⟨453,(3),[11],[2],1172⟩) from rfl))
private theorem rec15693 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(4),[11],[2],1173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[772]? = some (⟨453,(4),[11],[2],1173⟩) from rfl))
private theorem rec15695 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(5),[11],[2],1173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[774]? = some (⟨453,(5),[11],[2],1173⟩) from rfl))
private theorem rec15698 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(6),[11],[2],1173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[777]? = some (⟨453,(6),[11],[2],1173⟩) from rfl))
private theorem rec15700 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(7),[11],[2],1173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[779]? = some (⟨453,(7),[11],[2],1173⟩) from rfl))
private theorem rec15702 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(8),[11],[2],1175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[781]? = some (⟨453,(8),[11],[2],1175⟩) from rfl))
private theorem rec15704 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(9),[11],[2],1175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[783]? = some (⟨453,(9),[11],[2],1175⟩) from rfl))
private theorem rec15706 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(10),[11],[2],1175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[785]? = some (⟨453,(10),[11],[2],1175⟩) from rfl))
private theorem rec15708 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(11),[11],[2],1175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[787]? = some (⟨453,(11),[11],[2],1175⟩) from rfl))
private theorem rec15710 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(12),[11],[2],1176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[789]? = some (⟨453,(12),[11],[2],1176⟩) from rfl))
private theorem rec15712 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(13),[11],[2],1176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[791]? = some (⟨453,(13),[11],[2],1176⟩) from rfl))
private theorem rec15714 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(14),[11],[2],1176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[793]? = some (⟨453,(14),[11],[2],1176⟩) from rfl))
private theorem rec15716 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 453 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(15),[11],[2],1176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[795]? = some (⟨453,(15),[11],[2],1176⟩) from rfl))
private theorem rec15719 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 455 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨455,(0),[11],[2],1629⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[798]? = some (⟨455,(0),[11],[2],1629⟩) from rfl))
private theorem rec15721 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 455 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨455,(1),[11],[2],1178⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[800]? = some (⟨455,(1),[11],[2],1178⟩) from rfl))
private theorem rec15723 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 455 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨455,(2),[11],[2],1177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[802]? = some (⟨455,(2),[11],[2],1177⟩) from rfl))
private theorem rec15725 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 455 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨455,(3),[11],[2],1179⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[804]? = some (⟨455,(3),[11],[2],1179⟩) from rfl))
private theorem rec15727 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 458 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨458,(0),[11],[2],1180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[806]? = some (⟨458,(0),[11],[2],1180⟩) from rfl))
private theorem rec15729 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 458 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨458,(1),[11],[2],1181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[808]? = some (⟨458,(1),[11],[2],1181⟩) from rfl))
private theorem rec15731 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 458 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨458,(2),[11],[2],1182⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[810]? = some (⟨458,(2),[11],[2],1182⟩) from rfl))
private theorem rec15733 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 458 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨458,(3),[11],[2],1183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[812]? = some (⟨458,(3),[11],[2],1183⟩) from rfl))
private theorem rec15735 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 460 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨460,(0),[11],[2],1184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[814]? = some (⟨460,(0),[11],[2],1184⟩) from rfl))
private theorem rec15737 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 460 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨460,(1),[11],[2],958⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[816]? = some (⟨460,(1),[11],[2],958⟩) from rfl))
private theorem rec15739 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 460 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨460,(2),[11],[2],959⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[818]? = some (⟨460,(2),[11],[2],959⟩) from rfl))
private theorem rec15741 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 460 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨460,(3),[11],[2],960⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[820]? = some (⟨460,(3),[11],[2],960⟩) from rfl))
private theorem rec15743 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 460 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨460,(4),[11],[2],961⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[822]? = some (⟨460,(4),[11],[2],961⟩) from rfl))
private theorem rec15745 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 461 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨461,(8),[11],[2],1185⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[824]? = some (⟨461,(8),[11],[2],1185⟩) from rfl))
private theorem rec15747 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 461 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨461,(9),[11],[2],1186⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[826]? = some (⟨461,(9),[11],[2],1186⟩) from rfl))
private theorem rec15749 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 461 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨461,(10),[11],[2],1185⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[828]? = some (⟨461,(10),[11],[2],1185⟩) from rfl))
private theorem rec15751 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 461 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨461,(11),[11],[2],1187⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[830]? = some (⟨461,(11),[11],[2],1187⟩) from rfl))
private theorem rec15753 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 462 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨462,(0),[11],[2],1188⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[832]? = some (⟨462,(0),[11],[2],1188⟩) from rfl))
private theorem rec15755 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 462 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨462,(1),[11],[2],1189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[834]? = some (⟨462,(1),[11],[2],1189⟩) from rfl))
private theorem rec15757 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 462 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨462,(2),[11],[2],1190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[836]? = some (⟨462,(2),[11],[2],1190⟩) from rfl))
private theorem rec15759 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 462 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨462,(3),[11],[2],1191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[838]? = some (⟨462,(3),[11],[2],1191⟩) from rfl))
private theorem rec15761 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 462 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨462,(4),[11],[2],1192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[840]? = some (⟨462,(4),[11],[2],1192⟩) from rfl))
private theorem rec15763 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 464 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨464,(0),[11],[2],1193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[842]? = some (⟨464,(0),[11],[2],1193⟩) from rfl))
private theorem rec15765 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 464 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨464,(1),[11],[2],1194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[844]? = some (⟨464,(1),[11],[2],1194⟩) from rfl))
private theorem rec15767 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 464 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨464,(2),[11],[2],1195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[846]? = some (⟨464,(2),[11],[2],1195⟩) from rfl))
private theorem rec15769 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 464 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨464,(3),[11],[2],1196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[848]? = some (⟨464,(3),[11],[2],1196⟩) from rfl))
private theorem rec15771 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 465 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨465,(0),[11],[2],1197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[850]? = some (⟨465,(0),[11],[2],1197⟩) from rfl))
private theorem rec15773 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 465 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨465,(1),[11],[2],1198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[852]? = some (⟨465,(1),[11],[2],1198⟩) from rfl))
private theorem rec15775 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 465 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨465,(2),[11],[2],1197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[854]? = some (⟨465,(2),[11],[2],1197⟩) from rfl))
private theorem rec15777 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 465 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨465,(3),[11],[2],1199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[856]? = some (⟨465,(3),[11],[2],1199⟩) from rfl))
private theorem rec15779 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 466 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨466,(0),[11],[2],1200⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[858]? = some (⟨466,(0),[11],[2],1200⟩) from rfl))
private theorem rec15781 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 466 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨466,(1),[11],[2],1201⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[860]? = some (⟨466,(1),[11],[2],1201⟩) from rfl))
private theorem rec15783 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 466 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨466,(2),[11],[2],1202⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[862]? = some (⟨466,(2),[11],[2],1202⟩) from rfl))
private theorem rec15785 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 466 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨466,(3),[11],[2],1203⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[864]? = some (⟨466,(3),[11],[2],1203⟩) from rfl))
private theorem rec15787 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(0),[11],[2],1204⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[866]? = some (⟨468,(0),[11],[2],1204⟩) from rfl))
private theorem rec15789 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(1),[11],[2],1205⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[868]? = some (⟨468,(1),[11],[2],1205⟩) from rfl))
private theorem rec15791 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(2),[11],[2],1206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[870]? = some (⟨468,(2),[11],[2],1206⟩) from rfl))
private theorem rec15793 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(3),[11],[2],1207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[872]? = some (⟨468,(3),[11],[2],1207⟩) from rfl))
private theorem rec15795 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(4),[11],[2],1208⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[874]? = some (⟨468,(4),[11],[2],1208⟩) from rfl))
private theorem rec15797 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(5),[11],[2],1205⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[876]? = some (⟨468,(5),[11],[2],1205⟩) from rfl))
private theorem rec15799 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(6),[11],[2],1206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[878]? = some (⟨468,(6),[11],[2],1206⟩) from rfl))
private theorem rec15801 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(7),[11],[2],1207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[880]? = some (⟨468,(7),[11],[2],1207⟩) from rfl))
private theorem rec15803 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(8),[11],[2],1204⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[882]? = some (⟨468,(8),[11],[2],1204⟩) from rfl))
private theorem rec15805 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(9),[11],[2],1209⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[884]? = some (⟨468,(9),[11],[2],1209⟩) from rfl))
private theorem rec15807 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(10),[11],[2],1206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[886]? = some (⟨468,(10),[11],[2],1206⟩) from rfl))
private theorem rec15809 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(11),[11],[2],1207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[888]? = some (⟨468,(11),[11],[2],1207⟩) from rfl))
private theorem rec15811 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(12),[11],[2],1210⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[890]? = some (⟨468,(12),[11],[2],1210⟩) from rfl))
private theorem rec15813 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(13),[11],[2],1205⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[892]? = some (⟨468,(13),[11],[2],1205⟩) from rfl))
private theorem rec15815 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(14),[11],[2],1206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[894]? = some (⟨468,(14),[11],[2],1206⟩) from rfl))
private theorem rec15817 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 468 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(15),[11],[2],1207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[896]? = some (⟨468,(15),[11],[2],1207⟩) from rfl))
private theorem rec15819 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(0),[11],[2],1211⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[898]? = some (⟨470,(0),[11],[2],1211⟩) from rfl))
private theorem rec15821 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(1),[11],[2],1212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[900]? = some (⟨470,(1),[11],[2],1212⟩) from rfl))
private theorem rec15823 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(2),[11],[2],1213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[902]? = some (⟨470,(2),[11],[2],1213⟩) from rfl))
private theorem rec15825 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(3),[11],[2],1214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[904]? = some (⟨470,(3),[11],[2],1214⟩) from rfl))
private theorem rec15827 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(4),[11],[2],1215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[906]? = some (⟨470,(4),[11],[2],1215⟩) from rfl))
private theorem rec15829 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(5),[11],[2],1216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[908]? = some (⟨470,(5),[11],[2],1216⟩) from rfl))
private theorem rec15831 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(6),[11],[2],1217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[910]? = some (⟨470,(6),[11],[2],1217⟩) from rfl))
private theorem rec15833 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(7),[11],[2],1218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[912]? = some (⟨470,(7),[11],[2],1218⟩) from rfl))
private theorem rec15835 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(8),[11],[2],1219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[914]? = some (⟨470,(8),[11],[2],1219⟩) from rfl))
private theorem rec15837 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(9),[11],[2],1220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[916]? = some (⟨470,(9),[11],[2],1220⟩) from rfl))
private theorem rec15839 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(10),[11],[2],1221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[918]? = some (⟨470,(10),[11],[2],1221⟩) from rfl))
private theorem rec15841 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(11),[11],[2],1222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[920]? = some (⟨470,(11),[11],[2],1222⟩) from rfl))
private theorem rec15843 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(12),[11],[2],1223⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[922]? = some (⟨470,(12),[11],[2],1223⟩) from rfl))
private theorem rec15845 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(13),[11],[2],1220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[924]? = some (⟨470,(13),[11],[2],1220⟩) from rfl))
private theorem rec15847 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(14),[11],[2],1221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[926]? = some (⟨470,(14),[11],[2],1221⟩) from rfl))
private theorem rec15849 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 470 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(15),[11],[2],1222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[928]? = some (⟨470,(15),[11],[2],1222⟩) from rfl))
private theorem rec15851 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 471 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(0),[11],[2],1224⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[930]? = some (⟨471,(0),[11],[2],1224⟩) from rfl))
private theorem rec15853 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 471 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(1),[11],[2],1224⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[932]? = some (⟨471,(1),[11],[2],1224⟩) from rfl))
private theorem rec15855 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 471 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(2),[11],[2],1225⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[934]? = some (⟨471,(2),[11],[2],1225⟩) from rfl))
private theorem rec15857 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 471 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(3),[11],[2],1225⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[936]? = some (⟨471,(3),[11],[2],1225⟩) from rfl))
private theorem rec15859 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 471 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(4),[11],[2],1226⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[938]? = some (⟨471,(4),[11],[2],1226⟩) from rfl))
private theorem rec15861 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 471 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(5),[11],[2],1226⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[940]? = some (⟨471,(5),[11],[2],1226⟩) from rfl))
private theorem rec15863 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 471 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(6),[11],[2],1227⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[942]? = some (⟨471,(6),[11],[2],1227⟩) from rfl))
private theorem rec15865 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 471 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(7),[11],[2],1227⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[944]? = some (⟨471,(7),[11],[2],1227⟩) from rfl))
private theorem rec15867 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(0),[11],[2],1228⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[946]? = some (⟨472,(0),[11],[2],1228⟩) from rfl))
private theorem rec15869 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(1),[11],[2],1229⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[948]? = some (⟨472,(1),[11],[2],1229⟩) from rfl))
private theorem rec15871 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(2),[11],[2],1228⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[950]? = some (⟨472,(2),[11],[2],1228⟩) from rfl))
private theorem rec15873 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(3),[11],[2],1230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[952]? = some (⟨472,(3),[11],[2],1230⟩) from rfl))
private theorem rec15875 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(4),[11],[2],1231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[954]? = some (⟨472,(4),[11],[2],1231⟩) from rfl))
private theorem rec15877 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(5),[11],[2],1232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[956]? = some (⟨472,(5),[11],[2],1232⟩) from rfl))
private theorem rec15879 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(6),[11],[2],1233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[958]? = some (⟨472,(6),[11],[2],1233⟩) from rfl))
private theorem rec15881 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(7),[11],[2],1234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[960]? = some (⟨472,(7),[11],[2],1234⟩) from rfl))
private theorem rec15883 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(8),[11],[2],1235⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[962]? = some (⟨472,(8),[11],[2],1235⟩) from rfl))
private theorem rec15885 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(9),[11],[2],1236⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[964]? = some (⟨472,(9),[11],[2],1236⟩) from rfl))
private theorem rec15887 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(10),[11],[2],1237⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[966]? = some (⟨472,(10),[11],[2],1237⟩) from rfl))
private theorem rec15889 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(11),[11],[2],1238⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[968]? = some (⟨472,(11),[11],[2],1238⟩) from rfl))
private theorem rec15891 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(12),[11],[2],1239⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[970]? = some (⟨472,(12),[11],[2],1239⟩) from rfl))
private theorem rec15893 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(13),[11],[2],1240⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[972]? = some (⟨472,(13),[11],[2],1240⟩) from rfl))
private theorem rec15895 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(14),[11],[2],1241⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[974]? = some (⟨472,(14),[11],[2],1241⟩) from rfl))
private theorem rec15897 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(15),[11],[2],1241⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[976]? = some (⟨472,(15),[11],[2],1241⟩) from rfl))
private theorem rec15899 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(16),[11],[2],1242⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[978]? = some (⟨472,(16),[11],[2],1242⟩) from rfl))
private theorem rec15901 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(17),[11],[2],1243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[980]? = some (⟨472,(17),[11],[2],1243⟩) from rfl))
private theorem rec15903 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(18),[11],[2],1244⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[982]? = some (⟨472,(18),[11],[2],1244⟩) from rfl))
private theorem rec15905 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 472 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(19),[11],[2],1244⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[984]? = some (⟨472,(19),[11],[2],1244⟩) from rfl))
private theorem rec15907 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 474 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨474,(0),[11],[2],1245⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[986]? = some (⟨474,(0),[11],[2],1245⟩) from rfl))
private theorem rec15909 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 474 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨474,(1),[11],[2],1245⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[988]? = some (⟨474,(1),[11],[2],1245⟩) from rfl))
private theorem rec15911 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 474 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨474,(2),[11],[2],1246⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[990]? = some (⟨474,(2),[11],[2],1246⟩) from rfl))
private theorem rec15913 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 474 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨474,(3),[11],[2],1246⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[992]? = some (⟨474,(3),[11],[2],1246⟩) from rfl))
private theorem rec15915 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 474 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨474,(4),[11],[2],1247⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[994]? = some (⟨474,(4),[11],[2],1247⟩) from rfl))
private theorem rec15917 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 474 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨474,(5),[11],[2],1247⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[996]? = some (⟨474,(5),[11],[2],1247⟩) from rfl))
private theorem rec15919 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 474 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨474,(6),[11],[2],939⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[998]? = some (⟨474,(6),[11],[2],939⟩) from rfl))
private theorem rec15921 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 474 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨474,(7),[11],[2],939⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1000]? = some (⟨474,(7),[11],[2],939⟩) from rfl))
private theorem rec15923 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 474 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨474,(8),[11],[2],1248⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1002]? = some (⟨474,(8),[11],[2],1248⟩) from rfl))
private theorem rec15925 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 474 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨474,(9),[11],[2],1248⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1004]? = some (⟨474,(9),[11],[2],1248⟩) from rfl))
private theorem rec16532 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 606 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨606,(0),[11],[2],1649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[324]? = some (⟨606,(0),[11],[2],1649⟩) from rfl))
private theorem rec16533 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 606 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨606,(1),[11],[2],1672⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[325]? = some (⟨606,(1),[11],[2],1672⟩) from rfl))
private theorem rec16534 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 606 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨606,(2),[11],[2],1673⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[326]? = some (⟨606,(2),[11],[2],1673⟩) from rfl))
private theorem rec16535 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 606 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨606,(3),[11],[2],1674⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[327]? = some (⟨606,(3),[11],[2],1674⟩) from rfl))
private theorem rec16536 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 606 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨606,(4),[11],[2],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[328]? = some (⟨606,(4),[11],[2],890⟩) from rfl))
private theorem rec16537 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 606 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨606,(5),[11],[2],1649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[329]? = some (⟨606,(5),[11],[2],1649⟩) from rfl))
private theorem rec16538 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 606 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨606,(6),[11],[2],1672⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[330]? = some (⟨606,(6),[11],[2],1672⟩) from rfl))
private theorem rec16539 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 606 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨606,(7),[11],[2],1673⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[331]? = some (⟨606,(7),[11],[2],1673⟩) from rfl))
private theorem rec16540 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 606 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨606,(8),[11],[2],1674⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[332]? = some (⟨606,(8),[11],[2],1674⟩) from rfl))
private theorem rec16541 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 606 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨606,(9),[11],[2],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[333]? = some (⟨606,(9),[11],[2],890⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 11).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 11)).drop 0).take 4, section14Recorded section14Catalog 11 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 11 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 11).plans.drop 6).take 1 = [⟨9,413,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false,[(605,⟨([1],[]),true,([1],[]),false,false,[]⟩),(415,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(416,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(606,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(607,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(419,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(420,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(421,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(422,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(423,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(424,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(425,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(426,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(427,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(428,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(429,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(430,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(431,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(432,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(433,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(434,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(435,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(436,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(437,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(438,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(439,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(440,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(441,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(442,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(443,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(444,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(445,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(446,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(447,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(448,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(449,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(450,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(451,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(452,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(453,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(454,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(455,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(456,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(457,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(458,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(608,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(460,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(461,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(462,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(463,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(464,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(465,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(466,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(467,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(468,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(469,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(470,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(471,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(472,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(473,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(474,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(609,⟨([1],[]),true,([],[]),true,false,[]⟩),(476,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 11)).drop 0).take 4 = [⟨5,0,[⟨true,false,12⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨5,1,[⟨true,false,16⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨5,2,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨5,3,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · left
    exact rec15178 11 0 (by decide) (by decide)
  · left
    exact rec15185 11 1 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(605,⟨([1],[]),true,([1],[]),false,false,[]⟩),(415,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(416,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(606,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(607,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(419,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(420,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(421,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(422,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(423,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(424,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(425,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(426,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(427,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(428,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(429,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(430,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(431,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(432,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(433,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(434,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(435,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(436,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(437,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(438,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(439,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(440,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(441,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(442,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(443,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(444,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(445,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(446,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(447,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(448,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(449,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(450,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(451,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(452,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(453,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(454,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(455,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(456,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(457,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(458,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(608,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(460,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(461,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(462,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(463,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(464,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(465,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(466,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(467,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(468,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(469,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(470,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(471,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(472,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(473,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(474,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(609,⟨([1],[]),true,([],[]),true,false,[]⟩),(476,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 605)).length = 1 := by decide +kernel
      have hjj : j < 1 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 415)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15188 11 2 (by decide) (by decide)
      · right
        exact rec15190 11 2 (by decide) (by decide)
      · right
        exact rec15192 11 2 (by decide) (by decide)
      · right
        exact rec15194 11 2 (by decide) (by decide)
      · right
        exact rec15196 11 2 (by decide) (by decide)
      · right
        exact rec15198 11 2 (by decide) (by decide)
      · right
        exact rec15200 11 2 (by decide) (by decide)
      · right
        exact rec15202 11 2 (by decide) (by decide)
      · right
        exact rec15204 11 2 (by decide) (by decide)
      · right
        exact rec15206 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 416)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 606)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16532 11 2 (by decide) (by decide)
      · right
        exact rec16533 11 2 (by decide) (by decide)
      · right
        exact rec16534 11 2 (by decide) (by decide)
      · right
        exact rec16535 11 2 (by decide) (by decide)
      · right
        exact rec16536 11 2 (by decide) (by decide)
      · right
        exact rec16537 11 2 (by decide) (by decide)
      · right
        exact rec16538 11 2 (by decide) (by decide)
      · right
        exact rec16539 11 2 (by decide) (by decide)
      · right
        exact rec16540 11 2 (by decide) (by decide)
      · right
        exact rec16541 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 607)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 419)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 420)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15233 11 2 (by decide) (by decide)
      · right
        exact rec15235 11 2 (by decide) (by decide)
      · right
        exact rec15237 11 2 (by decide) (by decide)
      · right
        exact rec15239 11 2 (by decide) (by decide)
      · right
        exact rec15241 11 2 (by decide) (by decide)
      · right
        exact rec15243 11 2 (by decide) (by decide)
      · right
        exact rec15245 11 2 (by decide) (by decide)
      · right
        exact rec15247 11 2 (by decide) (by decide)
      · right
        exact rec15249 11 2 (by decide) (by decide)
      · right
        exact rec15251 11 2 (by decide) (by decide)
      · right
        exact rec15253 11 2 (by decide) (by decide)
      · right
        exact rec15255 11 2 (by decide) (by decide)
      · right
        exact rec15257 11 2 (by decide) (by decide)
      · right
        exact rec15259 11 2 (by decide) (by decide)
      · right
        exact rec15261 11 2 (by decide) (by decide)
      · right
        exact rec15263 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 421)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 422)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 423)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15265 11 2 (by decide) (by decide)
      · right
        exact rec15267 11 2 (by decide) (by decide)
      · right
        exact rec15269 11 2 (by decide) (by decide)
      · right
        exact rec15271 11 2 (by decide) (by decide)
      · right
        exact rec15273 11 2 (by decide) (by decide)
      · right
        exact rec15275 11 2 (by decide) (by decide)
      · right
        exact rec15277 11 2 (by decide) (by decide)
      · right
        exact rec15279 11 2 (by decide) (by decide)
      · right
        exact rec15281 11 2 (by decide) (by decide)
      · right
        exact rec15283 11 2 (by decide) (by decide)
      · right
        exact rec15285 11 2 (by decide) (by decide)
      · right
        exact rec15287 11 2 (by decide) (by decide)
      · right
        exact rec15289 11 2 (by decide) (by decide)
      · right
        exact rec15291 11 2 (by decide) (by decide)
      · right
        exact rec15293 11 2 (by decide) (by decide)
      · right
        exact rec15295 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 424)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 425)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 426)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15297 11 2 (by decide) (by decide)
      · right
        exact rec15299 11 2 (by decide) (by decide)
      · right
        exact rec15301 11 2 (by decide) (by decide)
      · right
        exact rec15303 11 2 (by decide) (by decide)
      · right
        exact rec15305 11 2 (by decide) (by decide)
      · right
        exact rec15307 11 2 (by decide) (by decide)
      · right
        exact rec15309 11 2 (by decide) (by decide)
      · right
        exact rec15311 11 2 (by decide) (by decide)
      · right
        exact rec15313 11 2 (by decide) (by decide)
      · right
        exact rec15315 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 427)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 428)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15317 11 2 (by decide) (by decide)
      · right
        exact rec15319 11 2 (by decide) (by decide)
      · right
        exact rec15321 11 2 (by decide) (by decide)
      · right
        exact rec15323 11 2 (by decide) (by decide)
      · right
        exact rec15325 11 2 (by decide) (by decide)
      · right
        exact rec15327 11 2 (by decide) (by decide)
      · right
        exact rec15329 11 2 (by decide) (by decide)
      · right
        exact rec15331 11 2 (by decide) (by decide)
      · right
        exact rec15333 11 2 (by decide) (by decide)
      · right
        exact rec15335 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 429)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 430)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 431)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15337 11 2 (by decide) (by decide)
      · right
        exact rec15339 11 2 (by decide) (by decide)
      · right
        exact rec15341 11 2 (by decide) (by decide)
      · right
        exact rec15343 11 2 (by decide) (by decide)
      · right
        exact rec15345 11 2 (by decide) (by decide)
      · right
        exact rec15347 11 2 (by decide) (by decide)
      · right
        exact rec15349 11 2 (by decide) (by decide)
      · right
        exact rec15351 11 2 (by decide) (by decide)
      · right
        exact rec15353 11 2 (by decide) (by decide)
      · right
        exact rec15355 11 2 (by decide) (by decide)
      · right
        exact rec15357 11 2 (by decide) (by decide)
      · right
        exact rec15359 11 2 (by decide) (by decide)
      · right
        exact rec15361 11 2 (by decide) (by decide)
      · right
        exact rec15363 11 2 (by decide) (by decide)
      · right
        exact rec15365 11 2 (by decide) (by decide)
      · right
        exact rec15367 11 2 (by decide) (by decide)
      · right
        exact rec15369 11 2 (by decide) (by decide)
      · right
        exact rec15371 11 2 (by decide) (by decide)
      · right
        exact rec15373 11 2 (by decide) (by decide)
      · right
        exact rec15375 11 2 (by decide) (by decide)
      · right
        exact rec15377 11 2 (by decide) (by decide)
      · right
        exact rec15379 11 2 (by decide) (by decide)
      · right
        exact rec15381 11 2 (by decide) (by decide)
      · right
        exact rec15383 11 2 (by decide) (by decide)
      · right
        exact rec15385 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 432)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 433)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15387 11 2 (by decide) (by decide)
      · right
        exact rec15389 11 2 (by decide) (by decide)
      · right
        exact rec15391 11 2 (by decide) (by decide)
      · right
        exact rec15393 11 2 (by decide) (by decide)
      · right
        exact rec15395 11 2 (by decide) (by decide)
      · right
        exact rec15397 11 2 (by decide) (by decide)
      · right
        exact rec15399 11 2 (by decide) (by decide)
      · right
        exact rec15401 11 2 (by decide) (by decide)
      · right
        exact rec15403 11 2 (by decide) (by decide)
      · right
        exact rec15405 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 434)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 435)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 436)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15407 11 2 (by decide) (by decide)
      · right
        exact rec15409 11 2 (by decide) (by decide)
      · right
        exact rec15411 11 2 (by decide) (by decide)
      · right
        exact rec15413 11 2 (by decide) (by decide)
      · right
        exact rec15415 11 2 (by decide) (by decide)
      · right
        exact rec15417 11 2 (by decide) (by decide)
      · right
        exact rec15419 11 2 (by decide) (by decide)
      · right
        exact rec15421 11 2 (by decide) (by decide)
      · right
        exact rec15423 11 2 (by decide) (by decide)
      · right
        exact rec15425 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 437)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 438)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15427 11 2 (by decide) (by decide)
      · right
        exact rec15429 11 2 (by decide) (by decide)
      · right
        exact rec15431 11 2 (by decide) (by decide)
      · right
        exact rec15433 11 2 (by decide) (by decide)
      · right
        exact rec15435 11 2 (by decide) (by decide)
      · right
        exact rec15437 11 2 (by decide) (by decide)
      · right
        exact rec15439 11 2 (by decide) (by decide)
      · right
        exact rec15441 11 2 (by decide) (by decide)
      · right
        exact rec15443 11 2 (by decide) (by decide)
      · right
        exact rec15445 11 2 (by decide) (by decide)
      · right
        exact rec15447 11 2 (by decide) (by decide)
      · right
        exact rec15449 11 2 (by decide) (by decide)
      · right
        exact rec15451 11 2 (by decide) (by decide)
      · right
        exact rec15453 11 2 (by decide) (by decide)
      · right
        exact rec15455 11 2 (by decide) (by decide)
      · right
        exact rec15457 11 2 (by decide) (by decide)
      · right
        exact rec15459 11 2 (by decide) (by decide)
      · right
        exact rec15461 11 2 (by decide) (by decide)
      · right
        exact rec15463 11 2 (by decide) (by decide)
      · right
        exact rec15465 11 2 (by decide) (by decide)
      · right
        exact rec15467 11 2 (by decide) (by decide)
      · right
        exact rec15469 11 2 (by decide) (by decide)
      · right
        exact rec15471 11 2 (by decide) (by decide)
      · right
        exact rec15473 11 2 (by decide) (by decide)
      · right
        exact rec15475 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 439)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 440)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 441)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15477 11 2 (by decide) (by decide)
      · right
        exact rec15479 11 2 (by decide) (by decide)
      · right
        exact rec15481 11 2 (by decide) (by decide)
      · right
        exact rec15483 11 2 (by decide) (by decide)
      · right
        exact rec15485 11 2 (by decide) (by decide)
      · right
        exact rec15487 11 2 (by decide) (by decide)
      · right
        exact rec15489 11 2 (by decide) (by decide)
      · right
        exact rec15491 11 2 (by decide) (by decide)
      · right
        exact rec15493 11 2 (by decide) (by decide)
      · right
        exact rec15495 11 2 (by decide) (by decide)
      · right
        exact rec15497 11 2 (by decide) (by decide)
      · right
        exact rec15499 11 2 (by decide) (by decide)
      · right
        exact rec15501 11 2 (by decide) (by decide)
      · right
        exact rec15503 11 2 (by decide) (by decide)
      · right
        exact rec15505 11 2 (by decide) (by decide)
      · right
        exact rec15507 11 2 (by decide) (by decide)
      · right
        exact rec15509 11 2 (by decide) (by decide)
      · right
        exact rec15511 11 2 (by decide) (by decide)
      · right
        exact rec15513 11 2 (by decide) (by decide)
      · right
        exact rec15515 11 2 (by decide) (by decide)
      · right
        exact rec15517 11 2 (by decide) (by decide)
      · right
        exact rec15519 11 2 (by decide) (by decide)
      · right
        exact rec15521 11 2 (by decide) (by decide)
      · right
        exact rec15523 11 2 (by decide) (by decide)
      · right
        exact rec15525 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 442)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 443)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15527 11 2 (by decide) (by decide)
      · right
        exact rec15529 11 2 (by decide) (by decide)
      · right
        exact rec15531 11 2 (by decide) (by decide)
      · right
        exact rec15533 11 2 (by decide) (by decide)
      · right
        exact rec15535 11 2 (by decide) (by decide)
      · right
        exact rec15537 11 2 (by decide) (by decide)
      · right
        exact rec15539 11 2 (by decide) (by decide)
      · right
        exact rec15541 11 2 (by decide) (by decide)
      · right
        exact rec15543 11 2 (by decide) (by decide)
      · right
        exact rec15545 11 2 (by decide) (by decide)
      · right
        exact rec15547 11 2 (by decide) (by decide)
      · right
        exact rec15549 11 2 (by decide) (by decide)
      · right
        exact rec15551 11 2 (by decide) (by decide)
      · right
        exact rec15553 11 2 (by decide) (by decide)
      · right
        exact rec15555 11 2 (by decide) (by decide)
      · right
        exact rec15557 11 2 (by decide) (by decide)
      · right
        exact rec15559 11 2 (by decide) (by decide)
      · right
        exact rec15561 11 2 (by decide) (by decide)
      · right
        exact rec15563 11 2 (by decide) (by decide)
      · right
        exact rec15565 11 2 (by decide) (by decide)
      · right
        exact rec15567 11 2 (by decide) (by decide)
      · right
        exact rec15569 11 2 (by decide) (by decide)
      · right
        exact rec15571 11 2 (by decide) (by decide)
      · right
        exact rec15573 11 2 (by decide) (by decide)
      · right
        exact rec15575 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 444)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 445)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 446)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15577 11 2 (by decide) (by decide)
      · right
        exact rec15579 11 2 (by decide) (by decide)
      · right
        exact rec15581 11 2 (by decide) (by decide)
      · right
        exact rec15583 11 2 (by decide) (by decide)
      · right
        exact rec15585 11 2 (by decide) (by decide)
      · right
        exact rec15587 11 2 (by decide) (by decide)
      · right
        exact rec15589 11 2 (by decide) (by decide)
      · right
        exact rec15591 11 2 (by decide) (by decide)
      · right
        exact rec15593 11 2 (by decide) (by decide)
      · right
        exact rec15595 11 2 (by decide) (by decide)
      · right
        exact rec15597 11 2 (by decide) (by decide)
      · right
        exact rec15599 11 2 (by decide) (by decide)
      · right
        exact rec15601 11 2 (by decide) (by decide)
      · right
        exact rec15603 11 2 (by decide) (by decide)
      · right
        exact rec15605 11 2 (by decide) (by decide)
      · right
        exact rec15607 11 2 (by decide) (by decide)
      · right
        exact rec15609 11 2 (by decide) (by decide)
      · right
        exact rec15611 11 2 (by decide) (by decide)
      · right
        exact rec15613 11 2 (by decide) (by decide)
      · right
        exact rec15615 11 2 (by decide) (by decide)
      · right
        exact rec15617 11 2 (by decide) (by decide)
      · right
        exact rec15619 11 2 (by decide) (by decide)
      · right
        exact rec15621 11 2 (by decide) (by decide)
      · right
        exact rec15623 11 2 (by decide) (by decide)
      · right
        exact rec15625 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 447)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 448)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15627 11 2 (by decide) (by decide)
      · right
        exact rec15629 11 2 (by decide) (by decide)
      · right
        exact rec15631 11 2 (by decide) (by decide)
      · right
        exact rec15633 11 2 (by decide) (by decide)
      · right
        exact rec15635 11 2 (by decide) (by decide)
      · right
        exact rec15637 11 2 (by decide) (by decide)
      · right
        exact rec15639 11 2 (by decide) (by decide)
      · right
        exact rec15641 11 2 (by decide) (by decide)
      · right
        exact rec15643 11 2 (by decide) (by decide)
      · right
        exact rec15645 11 2 (by decide) (by decide)
      · right
        exact rec15647 11 2 (by decide) (by decide)
      · right
        exact rec15649 11 2 (by decide) (by decide)
      · right
        exact rec15651 11 2 (by decide) (by decide)
      · right
        exact rec15653 11 2 (by decide) (by decide)
      · right
        exact rec15655 11 2 (by decide) (by decide)
      · right
        exact rec15657 11 2 (by decide) (by decide)
      · right
        exact rec15659 11 2 (by decide) (by decide)
      · right
        exact rec15661 11 2 (by decide) (by decide)
      · right
        exact rec15663 11 2 (by decide) (by decide)
      · right
        exact rec15665 11 2 (by decide) (by decide)
      · right
        exact rec15667 11 2 (by decide) (by decide)
      · right
        exact rec15669 11 2 (by decide) (by decide)
      · right
        exact rec15671 11 2 (by decide) (by decide)
      · right
        exact rec15673 11 2 (by decide) (by decide)
      · right
        exact rec15675 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 449)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 450)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15677 11 2 (by decide) (by decide)
      · right
        exact rec15679 11 2 (by decide) (by decide)
      · right
        exact rec15681 11 2 (by decide) (by decide)
      · right
        exact rec15683 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 451)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 452)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 453)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15685 11 2 (by decide) (by decide)
      · right
        exact rec15687 11 2 (by decide) (by decide)
      · right
        exact rec15689 11 2 (by decide) (by decide)
      · right
        exact rec15691 11 2 (by decide) (by decide)
      · right
        exact rec15693 11 2 (by decide) (by decide)
      · right
        exact rec15695 11 2 (by decide) (by decide)
      · right
        exact rec15698 11 2 (by decide) (by decide)
      · right
        exact rec15700 11 2 (by decide) (by decide)
      · right
        exact rec15702 11 2 (by decide) (by decide)
      · right
        exact rec15704 11 2 (by decide) (by decide)
      · right
        exact rec15706 11 2 (by decide) (by decide)
      · right
        exact rec15708 11 2 (by decide) (by decide)
      · right
        exact rec15710 11 2 (by decide) (by decide)
      · right
        exact rec15712 11 2 (by decide) (by decide)
      · right
        exact rec15714 11 2 (by decide) (by decide)
      · right
        exact rec15716 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 454)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 455)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15719 11 2 (by decide) (by decide)
      · right
        exact rec15721 11 2 (by decide) (by decide)
      · right
        exact rec15723 11 2 (by decide) (by decide)
      · right
        exact rec15725 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 456)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 457)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 458)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15727 11 2 (by decide) (by decide)
      · right
        exact rec15729 11 2 (by decide) (by decide)
      · right
        exact rec15731 11 2 (by decide) (by decide)
      · right
        exact rec15733 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 608)).length = 5 := by decide +kernel
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
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 460)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15735 11 2 (by decide) (by decide)
      · right
        exact rec15737 11 2 (by decide) (by decide)
      · right
        exact rec15739 11 2 (by decide) (by decide)
      · right
        exact rec15741 11 2 (by decide) (by decide)
      · right
        exact rec15743 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 461)).length = 20 := by decide +kernel
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
        exact rec15745 11 2 (by decide) (by decide)
      · right
        exact rec15747 11 2 (by decide) (by decide)
      · right
        exact rec15749 11 2 (by decide) (by decide)
      · right
        exact rec15751 11 2 (by decide) (by decide)
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 462)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15753 11 2 (by decide) (by decide)
      · right
        exact rec15755 11 2 (by decide) (by decide)
      · right
        exact rec15757 11 2 (by decide) (by decide)
      · right
        exact rec15759 11 2 (by decide) (by decide)
      · right
        exact rec15761 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 463)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 464)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15763 11 2 (by decide) (by decide)
      · right
        exact rec15765 11 2 (by decide) (by decide)
      · right
        exact rec15767 11 2 (by decide) (by decide)
      · right
        exact rec15769 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 465)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15771 11 2 (by decide) (by decide)
      · right
        exact rec15773 11 2 (by decide) (by decide)
      · right
        exact rec15775 11 2 (by decide) (by decide)
      · right
        exact rec15777 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 466)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15779 11 2 (by decide) (by decide)
      · right
        exact rec15781 11 2 (by decide) (by decide)
      · right
        exact rec15783 11 2 (by decide) (by decide)
      · right
        exact rec15785 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 467)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 468)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15787 11 2 (by decide) (by decide)
      · right
        exact rec15789 11 2 (by decide) (by decide)
      · right
        exact rec15791 11 2 (by decide) (by decide)
      · right
        exact rec15793 11 2 (by decide) (by decide)
      · right
        exact rec15795 11 2 (by decide) (by decide)
      · right
        exact rec15797 11 2 (by decide) (by decide)
      · right
        exact rec15799 11 2 (by decide) (by decide)
      · right
        exact rec15801 11 2 (by decide) (by decide)
      · right
        exact rec15803 11 2 (by decide) (by decide)
      · right
        exact rec15805 11 2 (by decide) (by decide)
      · right
        exact rec15807 11 2 (by decide) (by decide)
      · right
        exact rec15809 11 2 (by decide) (by decide)
      · right
        exact rec15811 11 2 (by decide) (by decide)
      · right
        exact rec15813 11 2 (by decide) (by decide)
      · right
        exact rec15815 11 2 (by decide) (by decide)
      · right
        exact rec15817 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 469)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 470)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15819 11 2 (by decide) (by decide)
      · right
        exact rec15821 11 2 (by decide) (by decide)
      · right
        exact rec15823 11 2 (by decide) (by decide)
      · right
        exact rec15825 11 2 (by decide) (by decide)
      · right
        exact rec15827 11 2 (by decide) (by decide)
      · right
        exact rec15829 11 2 (by decide) (by decide)
      · right
        exact rec15831 11 2 (by decide) (by decide)
      · right
        exact rec15833 11 2 (by decide) (by decide)
      · right
        exact rec15835 11 2 (by decide) (by decide)
      · right
        exact rec15837 11 2 (by decide) (by decide)
      · right
        exact rec15839 11 2 (by decide) (by decide)
      · right
        exact rec15841 11 2 (by decide) (by decide)
      · right
        exact rec15843 11 2 (by decide) (by decide)
      · right
        exact rec15845 11 2 (by decide) (by decide)
      · right
        exact rec15847 11 2 (by decide) (by decide)
      · right
        exact rec15849 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 471)).length = 8 := by decide +kernel
      have hjj : j < 8 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15851 11 2 (by decide) (by decide)
      · right
        exact rec15853 11 2 (by decide) (by decide)
      · right
        exact rec15855 11 2 (by decide) (by decide)
      · right
        exact rec15857 11 2 (by decide) (by decide)
      · right
        exact rec15859 11 2 (by decide) (by decide)
      · right
        exact rec15861 11 2 (by decide) (by decide)
      · right
        exact rec15863 11 2 (by decide) (by decide)
      · right
        exact rec15865 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 472)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15867 11 2 (by decide) (by decide)
      · right
        exact rec15869 11 2 (by decide) (by decide)
      · right
        exact rec15871 11 2 (by decide) (by decide)
      · right
        exact rec15873 11 2 (by decide) (by decide)
      · right
        exact rec15875 11 2 (by decide) (by decide)
      · right
        exact rec15877 11 2 (by decide) (by decide)
      · right
        exact rec15879 11 2 (by decide) (by decide)
      · right
        exact rec15881 11 2 (by decide) (by decide)
      · right
        exact rec15883 11 2 (by decide) (by decide)
      · right
        exact rec15885 11 2 (by decide) (by decide)
      · right
        exact rec15887 11 2 (by decide) (by decide)
      · right
        exact rec15889 11 2 (by decide) (by decide)
      · right
        exact rec15891 11 2 (by decide) (by decide)
      · right
        exact rec15893 11 2 (by decide) (by decide)
      · right
        exact rec15895 11 2 (by decide) (by decide)
      · right
        exact rec15897 11 2 (by decide) (by decide)
      · right
        exact rec15899 11 2 (by decide) (by decide)
      · right
        exact rec15901 11 2 (by decide) (by decide)
      · right
        exact rec15903 11 2 (by decide) (by decide)
      · right
        exact rec15905 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 473)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 474)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15907 11 2 (by decide) (by decide)
      · right
        exact rec15909 11 2 (by decide) (by decide)
      · right
        exact rec15911 11 2 (by decide) (by decide)
      · right
        exact rec15913 11 2 (by decide) (by decide)
      · right
        exact rec15915 11 2 (by decide) (by decide)
      · right
        exact rec15917 11 2 (by decide) (by decide)
      · right
        exact rec15919 11 2 (by decide) (by decide)
      · right
        exact rec15921 11 2 (by decide) (by decide)
      · right
        exact rec15923 11 2 (by decide) (by decide)
      · right
        exact rec15925 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 609)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 476)).length = 4 := by decide +kernel
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
  · left
    exact rec15186 11 3 (by decide) (by decide)
end Section14Coverage_11_6_p0_4

#print axioms solution
