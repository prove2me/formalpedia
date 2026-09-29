-- Prove2me | solution 1 for Freiman.section14_s0015_coverage0004_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T17:24:21.435794+00:00
-- url     : https://prove2.me/submissions/60fca1ca-e831-48e7-a318-8d741b0ae6f4

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
namespace Section14Coverage_15_4_p0_16
private theorem rec5553 (si parent : ℕ) (hs : si ∈ ([1, 2, 3, 5, 6, 7, 9, 10, 13, 14, 15] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],386⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[178]? = some (⟨82,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],386⟩) from rfl))
private theorem rec5570 (si parent : ℕ) (hs : si ∈ ([1, 3, 5, 7, 9, 11, 13, 15] : List ℕ)) (hp : parent ∈ ([0] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[1,3,5,7,9,11,13,15],[0],386⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[195]? = some (⟨82,(-1),[1,3,5,7,9,11,13,15],[0],386⟩) from rfl))
private theorem rec5583 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([5] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[3,4,7,8,12,15,16],[5],388⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[208]? = some (⟨82,(-1),[3,4,7,8,12,15,16],[5],388⟩) from rfl))
private theorem rec5584 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([2, 3] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[3,7,15],[2,3],386⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[209]? = some (⟨82,(-1),[3,7,15],[2,3],386⟩) from rfl))
private theorem rec5585 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([4, 6, 7] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[3,7,15],[4,6,7],388⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[210]? = some (⟨82,(-1),[3,7,15],[4,6,7],388⟩) from rfl))
private theorem rec5586 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[3,7,15],[8],390⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[211]? = some (⟨82,(-1),[3,7,15],[8],390⟩) from rfl))
private theorem rec5587 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[3,7,15],[9],392⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[212]? = some (⟨82,(-1),[3,7,15],[9],392⟩) from rfl))
private theorem rec5588 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[3,7,15],[11],628⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[213]? = some (⟨82,(-1),[3,7,15],[11],628⟩) from rfl))
private theorem rec5589 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([12, 13, 14, 15] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[3,7,15],[12,13,14,15],630⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[214]? = some (⟨82,(-1),[3,7,15],[12,13,14,15],630⟩) from rfl))
private theorem rec5590 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[3,7,15],[10],919⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[215]? = some (⟨82,(-1),[3,7,15],[10],919⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 15).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 15)).drop 0).take 16, section14Recorded section14Catalog 15 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 15 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 15).plans.drop 4).take 1 = [⟨5,82,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])],false,[(383,⟨([1],[]),true,([1],[]),false,false,[]⟩),(384,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(385,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(86,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(386,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(88,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(89,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(90,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(91,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(92,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(93,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(94,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(95,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(96,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(97,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(98,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(99,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(100,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(101,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(102,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(103,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(104,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(105,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(106,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(107,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(108,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(109,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(110,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(111,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(112,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(113,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(114,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(115,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(116,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(117,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(118,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(119,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(120,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(121,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(122,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(387,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(388,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(389,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(126,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(127,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(133,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(393,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(135,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(136,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(137,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(138,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(139,⟨([3,2],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(140,⟨([3,1,1],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(141,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(142,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(143,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(144,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(145,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(146,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(394,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(148,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(151,⟨([1],[]),true,([],[]),true,false,[]⟩),(650,⟨([],[]),false,([2],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 15)).drop 0).take 16 = [⟨2,0,[⟨true,false,12⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨2,1,[⟨true,false,12⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨2,2,[⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨2,3,[⟨true,false,12⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨2,4,[⟨true,false,16⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,5,[⟨true,false,16⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,6,[⟨true,true,11⟩,⟨true,false,16⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨2,7,[⟨true,false,16⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨2,8,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,9,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,10,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨2,11,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨2,12,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,13,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,14,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨2,15,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec5570 15 0 (by decide) (by decide)
  · left
    exact rec5553 15 1 (by decide) (by decide)
  · left
    exact rec5584 15 2 (by decide) (by decide)
  · left
    exact rec5584 15 3 (by decide) (by decide)
  · left
    exact rec5585 15 4 (by decide) (by decide)
  · left
    exact rec5583 15 5 (by decide) (by decide)
  · left
    exact rec5585 15 6 (by decide) (by decide)
  · left
    exact rec5585 15 7 (by decide) (by decide)
  · left
    exact rec5586 15 8 (by decide) (by decide)
  · left
    exact rec5587 15 9 (by decide) (by decide)
  · left
    exact rec5590 15 10 (by decide) (by decide)
  · left
    exact rec5588 15 11 (by decide) (by decide)
  · left
    exact rec5589 15 12 (by decide) (by decide)
  · left
    exact rec5589 15 13 (by decide) (by decide)
  · left
    exact rec5589 15 14 (by decide) (by decide)
  · left
    exact rec5589 15 15 (by decide) (by decide)
end Section14Coverage_15_4_p0_16

#print axioms solution
