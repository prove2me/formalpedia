-- Prove2me | solution 1 for Freiman.section14_s0011_coverage0005_parentidx0002_specs_0040_0048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T14:58:43.904155+00:00
-- url     : https://prove2.me/submissions/47537399-50e7-41cc-8406-cb489322f6a6

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
namespace Section14CoverageSpec_11_5_p2_40_48
private theorem rec9372 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 195 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(0),[11],[2],697⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1073]? = some (⟨195,(0),[11],[2],697⟩) from rfl))
private theorem rec9379 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 195 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(1),[11],[2],697⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1080]? = some (⟨195,(1),[11],[2],697⟩) from rfl))
private theorem rec9386 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 195 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(2),[11],[2],698⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1087]? = some (⟨195,(2),[11],[2],698⟩) from rfl))
private theorem rec9393 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 195 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(3),[11],[2],698⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1094]? = some (⟨195,(3),[11],[2],698⟩) from rfl))
private theorem rec9400 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 195 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(4),[11],[2],699⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1101]? = some (⟨195,(4),[11],[2],699⟩) from rfl))
private theorem rec9407 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 195 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(5),[11],[2],700⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1108]? = some (⟨195,(5),[11],[2],700⟩) from rfl))
private theorem rec9414 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 195 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(6),[11],[2],699⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1115]? = some (⟨195,(6),[11],[2],699⟩) from rfl))
private theorem rec9421 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 195 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(7),[11],[2],701⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1122]? = some (⟨195,(7),[11],[2],701⟩) from rfl))
private theorem rec9428 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 195 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(8),[11],[2],702⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1129]? = some (⟨195,(8),[11],[2],702⟩) from rfl))
private theorem rec9435 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 195 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(9),[11],[2],703⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1136]? = some (⟨195,(9),[11],[2],703⟩) from rfl))
private theorem rec9443 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(0),[11],[2],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1144]? = some (⟨197,(0),[11],[2],453⟩) from rfl))
private theorem rec9451 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(1),[11],[2],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1152]? = some (⟨197,(1),[11],[2],454⟩) from rfl))
private theorem rec9459 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(2),[11],[2],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1160]? = some (⟨197,(2),[11],[2],453⟩) from rfl))
private theorem rec9467 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(3),[11],[2],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1168]? = some (⟨197,(3),[11],[2],455⟩) from rfl))
private theorem rec9475 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(4),[11],[2],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1176]? = some (⟨197,(4),[11],[2],456⟩) from rfl))
private theorem rec9483 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(5),[11],[2],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1184]? = some (⟨197,(5),[11],[2],453⟩) from rfl))
private theorem rec9491 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(6),[11],[2],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1192]? = some (⟨197,(6),[11],[2],454⟩) from rfl))
private theorem rec9499 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(7),[11],[2],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1200]? = some (⟨197,(7),[11],[2],453⟩) from rfl))
private theorem rec9507 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(8),[11],[2],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1208]? = some (⟨197,(8),[11],[2],455⟩) from rfl))
private theorem rec9515 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(9),[11],[2],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1216]? = some (⟨197,(9),[11],[2],456⟩) from rfl))
private theorem rec9523 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(10),[11],[2],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[5]? = some (⟨197,(10),[11],[2],457⟩) from rfl))
private theorem rec9531 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(11),[11],[2],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[13]? = some (⟨197,(11),[11],[2],457⟩) from rfl))
private theorem rec9539 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(12),[11],[2],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[21]? = some (⟨197,(12),[11],[2],457⟩) from rfl))
private theorem rec9547 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(13),[11],[2],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[29]? = some (⟨197,(13),[11],[2],457⟩) from rfl))
private theorem rec9555 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(14),[11],[2],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[37]? = some (⟨197,(14),[11],[2],456⟩) from rfl))
private theorem rec9563 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(15),[11],[2],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[45]? = some (⟨197,(15),[11],[2],458⟩) from rfl))
private theorem rec9571 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(16),[11],[2],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[53]? = some (⟨197,(16),[11],[2],458⟩) from rfl))
private theorem rec9579 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(17),[11],[2],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[61]? = some (⟨197,(17),[11],[2],458⟩) from rfl))
private theorem rec9587 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(18),[11],[2],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[69]? = some (⟨197,(18),[11],[2],458⟩) from rfl))
private theorem rec9595 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(19),[11],[2],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[77]? = some (⟨197,(19),[11],[2],458⟩) from rfl))
private theorem rec9603 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(20),[11],[2],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[85]? = some (⟨197,(20),[11],[2],459⟩) from rfl))
private theorem rec9611 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(21),[11],[2],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[93]? = some (⟨197,(21),[11],[2],459⟩) from rfl))
private theorem rec9619 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(22),[11],[2],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[101]? = some (⟨197,(22),[11],[2],459⟩) from rfl))
private theorem rec9627 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(23),[11],[2],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[109]? = some (⟨197,(23),[11],[2],459⟩) from rfl))
private theorem rec9635 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 197 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(24),[11],[2],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[117]? = some (⟨197,(24),[11],[2],459⟩) from rfl))
private theorem rec9642 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(0),[11],[2],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[124]? = some (⟨200,(0),[11],[2],704⟩) from rfl))
private theorem rec9649 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(1),[11],[2],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[131]? = some (⟨200,(1),[11],[2],704⟩) from rfl))
private theorem rec9656 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(2),[11],[2],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[138]? = some (⟨200,(2),[11],[2],704⟩) from rfl))
private theorem rec9663 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(3),[11],[2],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[145]? = some (⟨200,(3),[11],[2],704⟩) from rfl))
private theorem rec9670 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(4),[11],[2],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[152]? = some (⟨200,(4),[11],[2],704⟩) from rfl))
private theorem rec9677 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(5),[11],[2],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[159]? = some (⟨200,(5),[11],[2],705⟩) from rfl))
private theorem rec9684 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(6),[11],[2],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[166]? = some (⟨200,(6),[11],[2],705⟩) from rfl))
private theorem rec9691 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(7),[11],[2],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[173]? = some (⟨200,(7),[11],[2],705⟩) from rfl))
private theorem rec9698 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(8),[11],[2],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[180]? = some (⟨200,(8),[11],[2],705⟩) from rfl))
private theorem rec9705 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(9),[11],[2],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[187]? = some (⟨200,(9),[11],[2],705⟩) from rfl))
private theorem rec9712 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(10),[11],[2],706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[194]? = some (⟨200,(10),[11],[2],706⟩) from rfl))
private theorem rec9719 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(11),[11],[2],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[201]? = some (⟨200,(11),[11],[2],707⟩) from rfl))
private theorem rec9726 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(12),[11],[2],708⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[208]? = some (⟨200,(12),[11],[2],708⟩) from rfl))
private theorem rec9733 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(13),[11],[2],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[215]? = some (⟨200,(13),[11],[2],707⟩) from rfl))
private theorem rec9740 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(14),[11],[2],709⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[222]? = some (⟨200,(14),[11],[2],709⟩) from rfl))
private theorem rec9747 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(15),[11],[2],706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[229]? = some (⟨200,(15),[11],[2],706⟩) from rfl))
private theorem rec9754 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(16),[11],[2],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[236]? = some (⟨200,(16),[11],[2],710⟩) from rfl))
private theorem rec9761 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(17),[11],[2],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[243]? = some (⟨200,(17),[11],[2],710⟩) from rfl))
private theorem rec9768 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(18),[11],[2],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[250]? = some (⟨200,(18),[11],[2],710⟩) from rfl))
private theorem rec9775 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(19),[11],[2],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[257]? = some (⟨200,(19),[11],[2],710⟩) from rfl))
private theorem rec9782 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(20),[11],[2],706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[264]? = some (⟨200,(20),[11],[2],706⟩) from rfl))
private theorem rec9789 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(21),[11],[2],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[271]? = some (⟨200,(21),[11],[2],707⟩) from rfl))
private theorem rec9796 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(22),[11],[2],708⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[278]? = some (⟨200,(22),[11],[2],708⟩) from rfl))
private theorem rec9803 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(23),[11],[2],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[285]? = some (⟨200,(23),[11],[2],707⟩) from rfl))
private theorem rec9810 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 200 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(24),[11],[2],709⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[292]? = some (⟨200,(24),[11],[2],709⟩) from rfl))
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 11).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 40).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 11 2 gs.1 j := by
  have hp : ((section14State section14Catalog 11).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(603,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(567,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(604,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(569,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(570,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  have hs : (((⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(603,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(567,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(604,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(569,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(570,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan).specs.drop 40).take 8) = [(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩)] := by rfl
  rw [hs]
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      exact rec9372 11 2 (by decide) (by decide)
    · right
      exact rec9379 11 2 (by decide) (by decide)
    · right
      exact rec9386 11 2 (by decide) (by decide)
    · right
      exact rec9393 11 2 (by decide) (by decide)
    · right
      exact rec9400 11 2 (by decide) (by decide)
    · right
      exact rec9407 11 2 (by decide) (by decide)
    · right
      exact rec9414 11 2 (by decide) (by decide)
    · right
      exact rec9421 11 2 (by decide) (by decide)
    · right
      exact rec9428 11 2 (by decide) (by decide)
    · right
      exact rec9435 11 2 (by decide) (by decide)
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
      exact rec9443 11 2 (by decide) (by decide)
    · right
      exact rec9451 11 2 (by decide) (by decide)
    · right
      exact rec9459 11 2 (by decide) (by decide)
    · right
      exact rec9467 11 2 (by decide) (by decide)
    · right
      exact rec9475 11 2 (by decide) (by decide)
    · right
      exact rec9483 11 2 (by decide) (by decide)
    · right
      exact rec9491 11 2 (by decide) (by decide)
    · right
      exact rec9499 11 2 (by decide) (by decide)
    · right
      exact rec9507 11 2 (by decide) (by decide)
    · right
      exact rec9515 11 2 (by decide) (by decide)
    · right
      exact rec9523 11 2 (by decide) (by decide)
    · right
      exact rec9531 11 2 (by decide) (by decide)
    · right
      exact rec9539 11 2 (by decide) (by decide)
    · right
      exact rec9547 11 2 (by decide) (by decide)
    · right
      exact rec9555 11 2 (by decide) (by decide)
    · right
      exact rec9563 11 2 (by decide) (by decide)
    · right
      exact rec9571 11 2 (by decide) (by decide)
    · right
      exact rec9579 11 2 (by decide) (by decide)
    · right
      exact rec9587 11 2 (by decide) (by decide)
    · right
      exact rec9595 11 2 (by decide) (by decide)
    · right
      exact rec9603 11 2 (by decide) (by decide)
    · right
      exact rec9611 11 2 (by decide) (by decide)
    · right
      exact rec9619 11 2 (by decide) (by decide)
    · right
      exact rec9627 11 2 (by decide) (by decide)
    · right
      exact rec9635 11 2 (by decide) (by decide)
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
      exact rec9642 11 2 (by decide) (by decide)
    · right
      exact rec9649 11 2 (by decide) (by decide)
    · right
      exact rec9656 11 2 (by decide) (by decide)
    · right
      exact rec9663 11 2 (by decide) (by decide)
    · right
      exact rec9670 11 2 (by decide) (by decide)
    · right
      exact rec9677 11 2 (by decide) (by decide)
    · right
      exact rec9684 11 2 (by decide) (by decide)
    · right
      exact rec9691 11 2 (by decide) (by decide)
    · right
      exact rec9698 11 2 (by decide) (by decide)
    · right
      exact rec9705 11 2 (by decide) (by decide)
    · right
      exact rec9712 11 2 (by decide) (by decide)
    · right
      exact rec9719 11 2 (by decide) (by decide)
    · right
      exact rec9726 11 2 (by decide) (by decide)
    · right
      exact rec9733 11 2 (by decide) (by decide)
    · right
      exact rec9740 11 2 (by decide) (by decide)
    · right
      exact rec9747 11 2 (by decide) (by decide)
    · right
      exact rec9754 11 2 (by decide) (by decide)
    · right
      exact rec9761 11 2 (by decide) (by decide)
    · right
      exact rec9768 11 2 (by decide) (by decide)
    · right
      exact rec9775 11 2 (by decide) (by decide)
    · right
      exact rec9782 11 2 (by decide) (by decide)
    · right
      exact rec9789 11 2 (by decide) (by decide)
    · right
      exact rec9796 11 2 (by decide) (by decide)
    · right
      exact rec9803 11 2 (by decide) (by decide)
    · right
      exact rec9810 11 2 (by decide) (by decide)
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
end Section14CoverageSpec_11_5_p2_40_48

#print axioms solution
