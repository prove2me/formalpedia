-- Prove2me | solution 1 for Freiman.section14_s0003_coverage0005_parentidx0011_specs_0048_0056
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T14:27:14.126118+00:00
-- url     : https://prove2.me/submissions/99313acc-d733-4f01-ac0a-6011e239cfba

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
namespace Section14CoverageSpec_3_5_p11_48_56
private theorem rec9812 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(0),[3,7],[11],1015⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[294]? = some (⟨202,(0),[3,7],[11],1015⟩) from rfl))
private theorem rec9820 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(1),[3,7],[11],1016⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[302]? = some (⟨202,(1),[3,7],[11],1016⟩) from rfl))
private theorem rec9828 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(2),[3,7],[11],1015⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[310]? = some (⟨202,(2),[3,7],[11],1015⟩) from rfl))
private theorem rec9836 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(3),[3,7],[11],1017⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[318]? = some (⟨202,(3),[3,7],[11],1017⟩) from rfl))
private theorem rec9844 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(4),[3,7],[11],1018⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[326]? = some (⟨202,(4),[3,7],[11],1018⟩) from rfl))
private theorem rec9852 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(5),[3,7],[11],1015⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[334]? = some (⟨202,(5),[3,7],[11],1015⟩) from rfl))
private theorem rec9860 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(6),[3,7],[11],1016⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[342]? = some (⟨202,(6),[3,7],[11],1016⟩) from rfl))
private theorem rec9868 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(7),[3,7],[11],1015⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[350]? = some (⟨202,(7),[3,7],[11],1015⟩) from rfl))
private theorem rec9876 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(8),[3,7],[11],1017⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[358]? = some (⟨202,(8),[3,7],[11],1017⟩) from rfl))
private theorem rec9884 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(9),[3,7],[11],1018⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[366]? = some (⟨202,(9),[3,7],[11],1018⟩) from rfl))
private theorem rec9892 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(10),[3,7],[11],1019⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[374]? = some (⟨202,(10),[3,7],[11],1019⟩) from rfl))
private theorem rec9900 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(11),[3,7],[11],1019⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[382]? = some (⟨202,(11),[3,7],[11],1019⟩) from rfl))
private theorem rec9908 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(12),[3,7],[11],1019⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[390]? = some (⟨202,(12),[3,7],[11],1019⟩) from rfl))
private theorem rec9916 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(13),[3,7],[11],1019⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[398]? = some (⟨202,(13),[3,7],[11],1019⟩) from rfl))
private theorem rec9924 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(14),[3,7],[11],1018⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[406]? = some (⟨202,(14),[3,7],[11],1018⟩) from rfl))
private theorem rec9932 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(15),[3,7],[11],1020⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[414]? = some (⟨202,(15),[3,7],[11],1020⟩) from rfl))
private theorem rec9940 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(16),[3,7],[11],1020⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[422]? = some (⟨202,(16),[3,7],[11],1020⟩) from rfl))
private theorem rec9948 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(17),[3,7],[11],1020⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[430]? = some (⟨202,(17),[3,7],[11],1020⟩) from rfl))
private theorem rec9956 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(18),[3,7],[11],1020⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[438]? = some (⟨202,(18),[3,7],[11],1020⟩) from rfl))
private theorem rec9964 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(19),[3,7],[11],1020⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[446]? = some (⟨202,(19),[3,7],[11],1020⟩) from rfl))
private theorem rec9972 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(20),[3,7],[11],1021⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[454]? = some (⟨202,(20),[3,7],[11],1021⟩) from rfl))
private theorem rec9980 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(21),[3,7],[11],1021⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[462]? = some (⟨202,(21),[3,7],[11],1021⟩) from rfl))
private theorem rec9988 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(22),[3,7],[11],1021⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[470]? = some (⟨202,(22),[3,7],[11],1021⟩) from rfl))
private theorem rec9996 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(23),[3,7],[11],1021⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[478]? = some (⟨202,(23),[3,7],[11],1021⟩) from rfl))
private theorem rec10004 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 202 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(24),[3,7],[11],1021⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[486]? = some (⟨202,(24),[3,7],[11],1021⟩) from rfl))
private theorem rec10013 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(0),[3,7],[11],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[495]? = some (⟨205,(0),[3,7],[11],711⟩) from rfl))
private theorem rec10020 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(1),[3,7],[11],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[502]? = some (⟨205,(1),[3,7],[11],711⟩) from rfl))
private theorem rec10027 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(2),[3,7],[11],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[509]? = some (⟨205,(2),[3,7],[11],711⟩) from rfl))
private theorem rec10034 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(3),[3,7],[11],712⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[516]? = some (⟨205,(3),[3,7],[11],712⟩) from rfl))
private theorem rec10040 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(4),[3,7],[11],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[522]? = some (⟨205,(4),[3,7],[11],711⟩) from rfl))
private theorem rec10047 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(5),[3,7],[11],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[529]? = some (⟨205,(5),[3,7],[11],713⟩) from rfl))
private theorem rec10054 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(6),[3,7],[11],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[536]? = some (⟨205,(6),[3,7],[11],713⟩) from rfl))
private theorem rec10061 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(7),[3,7],[11],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[543]? = some (⟨205,(7),[3,7],[11],713⟩) from rfl))
private theorem rec10068 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(8),[3,7],[11],714⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[550]? = some (⟨205,(8),[3,7],[11],714⟩) from rfl))
private theorem rec10074 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(9),[3,7],[11],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[556]? = some (⟨205,(9),[3,7],[11],713⟩) from rfl))
private theorem rec10081 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(10),[3,7],[11],715⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[563]? = some (⟨205,(10),[3,7],[11],715⟩) from rfl))
private theorem rec10088 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(11),[3,7],[11],716⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[570]? = some (⟨205,(11),[3,7],[11],716⟩) from rfl))
private theorem rec10095 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(12),[3,7],[11],717⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[577]? = some (⟨205,(12),[3,7],[11],717⟩) from rfl))
private theorem rec10102 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(13),[3,7],[11],718⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[584]? = some (⟨205,(13),[3,7],[11],718⟩) from rfl))
private theorem rec10108 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(14),[3,7],[11],719⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[590]? = some (⟨205,(14),[3,7],[11],719⟩) from rfl))
private theorem rec10115 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(15),[3,7],[11],715⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[597]? = some (⟨205,(15),[3,7],[11],715⟩) from rfl))
private theorem rec10122 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(16),[3,7],[11],720⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[604]? = some (⟨205,(16),[3,7],[11],720⟩) from rfl))
private theorem rec10129 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(17),[3,7],[11],720⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[611]? = some (⟨205,(17),[3,7],[11],720⟩) from rfl))
private theorem rec10136 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(18),[3,7],[11],721⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[618]? = some (⟨205,(18),[3,7],[11],721⟩) from rfl))
private theorem rec10142 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(19),[3,7],[11],720⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[624]? = some (⟨205,(19),[3,7],[11],720⟩) from rfl))
private theorem rec10149 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(20),[3,7],[11],715⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[631]? = some (⟨205,(20),[3,7],[11],715⟩) from rfl))
private theorem rec10156 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(21),[3,7],[11],716⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[638]? = some (⟨205,(21),[3,7],[11],716⟩) from rfl))
private theorem rec10163 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(22),[3,7],[11],717⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[645]? = some (⟨205,(22),[3,7],[11],717⟩) from rfl))
private theorem rec10170 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(23),[3,7],[11],718⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[652]? = some (⟨205,(23),[3,7],[11],718⟩) from rfl))
private theorem rec10176 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 205 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(24),[3,7],[11],719⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[658]? = some (⟨205,(24),[3,7],[11],719⟩) from rfl))
private theorem rec10182 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(0),[3,7],[11],1022⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[664]? = some (⟨207,(0),[3,7],[11],1022⟩) from rfl))
private theorem rec10190 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(1),[3,7],[11],1023⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[672]? = some (⟨207,(1),[3,7],[11],1023⟩) from rfl))
private theorem rec10198 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(2),[3,7],[11],1022⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[680]? = some (⟨207,(2),[3,7],[11],1022⟩) from rfl))
private theorem rec10206 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(3),[3,7],[11],1024⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[688]? = some (⟨207,(3),[3,7],[11],1024⟩) from rfl))
private theorem rec10214 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(4),[3,7],[11],1025⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[696]? = some (⟨207,(4),[3,7],[11],1025⟩) from rfl))
private theorem rec10222 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(5),[3,7],[11],1022⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[704]? = some (⟨207,(5),[3,7],[11],1022⟩) from rfl))
private theorem rec10230 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(6),[3,7],[11],1023⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[712]? = some (⟨207,(6),[3,7],[11],1023⟩) from rfl))
private theorem rec10238 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(7),[3,7],[11],1022⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[720]? = some (⟨207,(7),[3,7],[11],1022⟩) from rfl))
private theorem rec10246 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(8),[3,7],[11],1024⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[728]? = some (⟨207,(8),[3,7],[11],1024⟩) from rfl))
private theorem rec10254 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(9),[3,7],[11],1025⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[736]? = some (⟨207,(9),[3,7],[11],1025⟩) from rfl))
private theorem rec10262 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(10),[3,7],[11],1026⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[744]? = some (⟨207,(10),[3,7],[11],1026⟩) from rfl))
private theorem rec10270 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(11),[3,7],[11],1026⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[752]? = some (⟨207,(11),[3,7],[11],1026⟩) from rfl))
private theorem rec10278 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(12),[3,7],[11],1026⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[760]? = some (⟨207,(12),[3,7],[11],1026⟩) from rfl))
private theorem rec10286 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(13),[3,7],[11],1026⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[768]? = some (⟨207,(13),[3,7],[11],1026⟩) from rfl))
private theorem rec10294 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(14),[3,7],[11],1025⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[776]? = some (⟨207,(14),[3,7],[11],1025⟩) from rfl))
private theorem rec10302 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(15),[3,7],[11],1027⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[784]? = some (⟨207,(15),[3,7],[11],1027⟩) from rfl))
private theorem rec10310 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(16),[3,7],[11],1027⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[792]? = some (⟨207,(16),[3,7],[11],1027⟩) from rfl))
private theorem rec10318 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(17),[3,7],[11],1027⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[800]? = some (⟨207,(17),[3,7],[11],1027⟩) from rfl))
private theorem rec10326 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(18),[3,7],[11],1027⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[808]? = some (⟨207,(18),[3,7],[11],1027⟩) from rfl))
private theorem rec10334 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(19),[3,7],[11],1027⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[816]? = some (⟨207,(19),[3,7],[11],1027⟩) from rfl))
private theorem rec10342 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(20),[3,7],[11],1028⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[824]? = some (⟨207,(20),[3,7],[11],1028⟩) from rfl))
private theorem rec10350 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(21),[3,7],[11],1028⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[832]? = some (⟨207,(21),[3,7],[11],1028⟩) from rfl))
private theorem rec10358 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(22),[3,7],[11],1028⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[840]? = some (⟨207,(22),[3,7],[11],1028⟩) from rfl))
private theorem rec10366 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(23),[3,7],[11],1028⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[848]? = some (⟨207,(23),[3,7],[11],1028⟩) from rfl))
private theorem rec10374 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 207 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(24),[3,7],[11],1028⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[856]? = some (⟨207,(24),[3,7],[11],1028⟩) from rfl))
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 48).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 11 gs.1 j := by
  have hp : ((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(398,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(401,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  have hs : (((⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(398,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(401,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan).specs.drop 48).take 8) = [(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩)] := by rfl
  rw [hs]
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 202)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec9812 3 11 (by decide) (by decide)
    · right
      exact rec9820 3 11 (by decide) (by decide)
    · right
      exact rec9828 3 11 (by decide) (by decide)
    · right
      exact rec9836 3 11 (by decide) (by decide)
    · right
      exact rec9844 3 11 (by decide) (by decide)
    · right
      exact rec9852 3 11 (by decide) (by decide)
    · right
      exact rec9860 3 11 (by decide) (by decide)
    · right
      exact rec9868 3 11 (by decide) (by decide)
    · right
      exact rec9876 3 11 (by decide) (by decide)
    · right
      exact rec9884 3 11 (by decide) (by decide)
    · right
      exact rec9892 3 11 (by decide) (by decide)
    · right
      exact rec9900 3 11 (by decide) (by decide)
    · right
      exact rec9908 3 11 (by decide) (by decide)
    · right
      exact rec9916 3 11 (by decide) (by decide)
    · right
      exact rec9924 3 11 (by decide) (by decide)
    · right
      exact rec9932 3 11 (by decide) (by decide)
    · right
      exact rec9940 3 11 (by decide) (by decide)
    · right
      exact rec9948 3 11 (by decide) (by decide)
    · right
      exact rec9956 3 11 (by decide) (by decide)
    · right
      exact rec9964 3 11 (by decide) (by decide)
    · right
      exact rec9972 3 11 (by decide) (by decide)
    · right
      exact rec9980 3 11 (by decide) (by decide)
    · right
      exact rec9988 3 11 (by decide) (by decide)
    · right
      exact rec9996 3 11 (by decide) (by decide)
    · right
      exact rec10004 3 11 (by decide) (by decide)
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
      exact rec10013 3 11 (by decide) (by decide)
    · right
      exact rec10020 3 11 (by decide) (by decide)
    · right
      exact rec10027 3 11 (by decide) (by decide)
    · right
      exact rec10034 3 11 (by decide) (by decide)
    · right
      exact rec10040 3 11 (by decide) (by decide)
    · right
      exact rec10047 3 11 (by decide) (by decide)
    · right
      exact rec10054 3 11 (by decide) (by decide)
    · right
      exact rec10061 3 11 (by decide) (by decide)
    · right
      exact rec10068 3 11 (by decide) (by decide)
    · right
      exact rec10074 3 11 (by decide) (by decide)
    · right
      exact rec10081 3 11 (by decide) (by decide)
    · right
      exact rec10088 3 11 (by decide) (by decide)
    · right
      exact rec10095 3 11 (by decide) (by decide)
    · right
      exact rec10102 3 11 (by decide) (by decide)
    · right
      exact rec10108 3 11 (by decide) (by decide)
    · right
      exact rec10115 3 11 (by decide) (by decide)
    · right
      exact rec10122 3 11 (by decide) (by decide)
    · right
      exact rec10129 3 11 (by decide) (by decide)
    · right
      exact rec10136 3 11 (by decide) (by decide)
    · right
      exact rec10142 3 11 (by decide) (by decide)
    · right
      exact rec10149 3 11 (by decide) (by decide)
    · right
      exact rec10156 3 11 (by decide) (by decide)
    · right
      exact rec10163 3 11 (by decide) (by decide)
    · right
      exact rec10170 3 11 (by decide) (by decide)
    · right
      exact rec10176 3 11 (by decide) (by decide)
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
      exact rec10182 3 11 (by decide) (by decide)
    · right
      exact rec10190 3 11 (by decide) (by decide)
    · right
      exact rec10198 3 11 (by decide) (by decide)
    · right
      exact rec10206 3 11 (by decide) (by decide)
    · right
      exact rec10214 3 11 (by decide) (by decide)
    · right
      exact rec10222 3 11 (by decide) (by decide)
    · right
      exact rec10230 3 11 (by decide) (by decide)
    · right
      exact rec10238 3 11 (by decide) (by decide)
    · right
      exact rec10246 3 11 (by decide) (by decide)
    · right
      exact rec10254 3 11 (by decide) (by decide)
    · right
      exact rec10262 3 11 (by decide) (by decide)
    · right
      exact rec10270 3 11 (by decide) (by decide)
    · right
      exact rec10278 3 11 (by decide) (by decide)
    · right
      exact rec10286 3 11 (by decide) (by decide)
    · right
      exact rec10294 3 11 (by decide) (by decide)
    · right
      exact rec10302 3 11 (by decide) (by decide)
    · right
      exact rec10310 3 11 (by decide) (by decide)
    · right
      exact rec10318 3 11 (by decide) (by decide)
    · right
      exact rec10326 3 11 (by decide) (by decide)
    · right
      exact rec10334 3 11 (by decide) (by decide)
    · right
      exact rec10342 3 11 (by decide) (by decide)
    · right
      exact rec10350 3 11 (by decide) (by decide)
    · right
      exact rec10358 3 11 (by decide) (by decide)
    · right
      exact rec10366 3 11 (by decide) (by decide)
    · right
      exact rec10374 3 11 (by decide) (by decide)
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
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 402)).length = 10 := by decide +kernel
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
end Section14CoverageSpec_3_5_p11_48_56

#print axioms solution
