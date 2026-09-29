-- Prove2me | solution 1 for Freiman.section14_s0003_coverage0005_parentidx0011_specs_0008_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T14:05:50.240827+00:00
-- url     : https://prove2.me/submissions/d07da740-6c48-4128-a210-e03c16443e77

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
namespace Section14CoverageSpec_3_5_p11_8_16
private theorem rec7748 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(0),[3,7],[11],965⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[64]? = some (⟨163,(0),[3,7],[11],965⟩) from rfl))
private theorem rec7756 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(1),[3,7],[11],966⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[72]? = some (⟨163,(1),[3,7],[11],966⟩) from rfl))
private theorem rec7764 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(2),[3,7],[11],965⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[80]? = some (⟨163,(2),[3,7],[11],965⟩) from rfl))
private theorem rec7772 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(3),[3,7],[11],967⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[88]? = some (⟨163,(3),[3,7],[11],967⟩) from rfl))
private theorem rec7780 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(4),[3,7],[11],968⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[96]? = some (⟨163,(4),[3,7],[11],968⟩) from rfl))
private theorem rec7788 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(5),[3,7],[11],968⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[104]? = some (⟨163,(5),[3,7],[11],968⟩) from rfl))
private theorem rec7796 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(6),[3,7],[11],968⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[112]? = some (⟨163,(6),[3,7],[11],968⟩) from rfl))
private theorem rec7804 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(7),[3,7],[11],968⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[120]? = some (⟨163,(7),[3,7],[11],968⟩) from rfl))
private theorem rec7812 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(8),[3,7],[11],969⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[128]? = some (⟨163,(8),[3,7],[11],969⟩) from rfl))
private theorem rec7820 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(9),[3,7],[11],969⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[136]? = some (⟨163,(9),[3,7],[11],969⟩) from rfl))
private theorem rec7828 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(10),[3,7],[11],969⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[144]? = some (⟨163,(10),[3,7],[11],969⟩) from rfl))
private theorem rec7836 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(11),[3,7],[11],969⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[152]? = some (⟨163,(11),[3,7],[11],969⟩) from rfl))
private theorem rec7844 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(12),[3,7],[11],970⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[160]? = some (⟨163,(12),[3,7],[11],970⟩) from rfl))
private theorem rec7852 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(13),[3,7],[11],970⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[168]? = some (⟨163,(13),[3,7],[11],970⟩) from rfl))
private theorem rec7860 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(14),[3,7],[11],970⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[176]? = some (⟨163,(14),[3,7],[11],970⟩) from rfl))
private theorem rec7868 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 163 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(15),[3,7],[11],970⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[184]? = some (⟨163,(15),[3,7],[11],970⟩) from rfl))
private theorem rec7877 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(0),[3,7],[11],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[193]? = some (⟨166,(0),[3,7],[11],644⟩) from rfl))
private theorem rec7884 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(1),[3,7],[11],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[200]? = some (⟨166,(1),[3,7],[11],644⟩) from rfl))
private theorem rec7891 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(2),[3,7],[11],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[207]? = some (⟨166,(2),[3,7],[11],644⟩) from rfl))
private theorem rec7898 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(3),[3,7],[11],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[214]? = some (⟨166,(3),[3,7],[11],644⟩) from rfl))
private theorem rec7905 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(4),[3,7],[11],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[221]? = some (⟨166,(4),[3,7],[11],645⟩) from rfl))
private theorem rec7912 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(5),[3,7],[11],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[228]? = some (⟨166,(5),[3,7],[11],645⟩) from rfl))
private theorem rec7919 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(6),[3,7],[11],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[235]? = some (⟨166,(6),[3,7],[11],645⟩) from rfl))
private theorem rec7926 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(7),[3,7],[11],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[242]? = some (⟨166,(7),[3,7],[11],645⟩) from rfl))
private theorem rec7933 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(8),[3,7],[11],646⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[249]? = some (⟨166,(8),[3,7],[11],646⟩) from rfl))
private theorem rec7940 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(9),[3,7],[11],647⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[256]? = some (⟨166,(9),[3,7],[11],647⟩) from rfl))
private theorem rec7947 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(10),[3,7],[11],646⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[263]? = some (⟨166,(10),[3,7],[11],646⟩) from rfl))
private theorem rec7954 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(11),[3,7],[11],648⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[270]? = some (⟨166,(11),[3,7],[11],648⟩) from rfl))
private theorem rec7961 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(12),[3,7],[11],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[277]? = some (⟨166,(12),[3,7],[11],649⟩) from rfl))
private theorem rec7968 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(13),[3,7],[11],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[284]? = some (⟨166,(13),[3,7],[11],649⟩) from rfl))
private theorem rec7975 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(14),[3,7],[11],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[291]? = some (⟨166,(14),[3,7],[11],649⟩) from rfl))
private theorem rec7982 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 166 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(15),[3,7],[11],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[298]? = some (⟨166,(15),[3,7],[11],649⟩) from rfl))
private theorem rec7988 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(0),[3,7],[11],971⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[304]? = some (⟨167,(0),[3,7],[11],971⟩) from rfl))
private theorem rec7996 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(1),[3,7],[11],972⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[312]? = some (⟨167,(1),[3,7],[11],972⟩) from rfl))
private theorem rec8004 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(2),[3,7],[11],973⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[320]? = some (⟨167,(2),[3,7],[11],973⟩) from rfl))
private theorem rec8012 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(3),[3,7],[11],974⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[328]? = some (⟨167,(3),[3,7],[11],974⟩) from rfl))
private theorem rec8020 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(4),[3,7],[11],975⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[336]? = some (⟨167,(4),[3,7],[11],975⟩) from rfl))
private theorem rec8028 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(5),[3,7],[11],972⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[344]? = some (⟨167,(5),[3,7],[11],972⟩) from rfl))
private theorem rec8036 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(6),[3,7],[11],973⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[352]? = some (⟨167,(6),[3,7],[11],973⟩) from rfl))
private theorem rec8044 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(7),[3,7],[11],974⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[360]? = some (⟨167,(7),[3,7],[11],974⟩) from rfl))
private theorem rec8052 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(8),[3,7],[11],971⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[368]? = some (⟨167,(8),[3,7],[11],971⟩) from rfl))
private theorem rec8060 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(9),[3,7],[11],972⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[376]? = some (⟨167,(9),[3,7],[11],972⟩) from rfl))
private theorem rec8068 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(10),[3,7],[11],973⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[384]? = some (⟨167,(10),[3,7],[11],973⟩) from rfl))
private theorem rec8076 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(11),[3,7],[11],974⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[392]? = some (⟨167,(11),[3,7],[11],974⟩) from rfl))
private theorem rec8084 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(12),[3,7],[11],976⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[400]? = some (⟨167,(12),[3,7],[11],976⟩) from rfl))
private theorem rec8092 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(13),[3,7],[11],972⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[408]? = some (⟨167,(13),[3,7],[11],972⟩) from rfl))
private theorem rec8100 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(14),[3,7],[11],973⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[416]? = some (⟨167,(14),[3,7],[11],973⟩) from rfl))
private theorem rec8108 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 167 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(15),[3,7],[11],974⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[424]? = some (⟨167,(15),[3,7],[11],974⟩) from rfl))
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 8).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 11 gs.1 j := by
  have hp : ((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(398,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(401,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  have hs : (((⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(398,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(401,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan).specs.drop 8).take 8) = [(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩)] := by rfl
  rw [hs]
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      exact rec7748 3 11 (by decide) (by decide)
    · right
      exact rec7756 3 11 (by decide) (by decide)
    · right
      exact rec7764 3 11 (by decide) (by decide)
    · right
      exact rec7772 3 11 (by decide) (by decide)
    · right
      exact rec7780 3 11 (by decide) (by decide)
    · right
      exact rec7788 3 11 (by decide) (by decide)
    · right
      exact rec7796 3 11 (by decide) (by decide)
    · right
      exact rec7804 3 11 (by decide) (by decide)
    · right
      exact rec7812 3 11 (by decide) (by decide)
    · right
      exact rec7820 3 11 (by decide) (by decide)
    · right
      exact rec7828 3 11 (by decide) (by decide)
    · right
      exact rec7836 3 11 (by decide) (by decide)
    · right
      exact rec7844 3 11 (by decide) (by decide)
    · right
      exact rec7852 3 11 (by decide) (by decide)
    · right
      exact rec7860 3 11 (by decide) (by decide)
    · right
      exact rec7868 3 11 (by decide) (by decide)
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
      exact rec7877 3 11 (by decide) (by decide)
    · right
      exact rec7884 3 11 (by decide) (by decide)
    · right
      exact rec7891 3 11 (by decide) (by decide)
    · right
      exact rec7898 3 11 (by decide) (by decide)
    · right
      exact rec7905 3 11 (by decide) (by decide)
    · right
      exact rec7912 3 11 (by decide) (by decide)
    · right
      exact rec7919 3 11 (by decide) (by decide)
    · right
      exact rec7926 3 11 (by decide) (by decide)
    · right
      exact rec7933 3 11 (by decide) (by decide)
    · right
      exact rec7940 3 11 (by decide) (by decide)
    · right
      exact rec7947 3 11 (by decide) (by decide)
    · right
      exact rec7954 3 11 (by decide) (by decide)
    · right
      exact rec7961 3 11 (by decide) (by decide)
    · right
      exact rec7968 3 11 (by decide) (by decide)
    · right
      exact rec7975 3 11 (by decide) (by decide)
    · right
      exact rec7982 3 11 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 167)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec7988 3 11 (by decide) (by decide)
    · right
      exact rec7996 3 11 (by decide) (by decide)
    · right
      exact rec8004 3 11 (by decide) (by decide)
    · right
      exact rec8012 3 11 (by decide) (by decide)
    · right
      exact rec8020 3 11 (by decide) (by decide)
    · right
      exact rec8028 3 11 (by decide) (by decide)
    · right
      exact rec8036 3 11 (by decide) (by decide)
    · right
      exact rec8044 3 11 (by decide) (by decide)
    · right
      exact rec8052 3 11 (by decide) (by decide)
    · right
      exact rec8060 3 11 (by decide) (by decide)
    · right
      exact rec8068 3 11 (by decide) (by decide)
    · right
      exact rec8076 3 11 (by decide) (by decide)
    · right
      exact rec8084 3 11 (by decide) (by decide)
    · right
      exact rec8092 3 11 (by decide) (by decide)
    · right
      exact rec8100 3 11 (by decide) (by decide)
    · right
      exact rec8108 3 11 (by decide) (by decide)
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
end Section14CoverageSpec_3_5_p11_8_16

#print axioms solution
