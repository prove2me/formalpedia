-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_coverage0006_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:41:16.482289+00:00
-- url     : https://prove2.me/submissions/b0ca1d0f-9acb-4a77-ad78-d4049a8bfd45

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0000_0016
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p0_16
private theorem rec12929 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 9, 10, 13, 14] : List ℕ)) (hp : parent ∈ ([2, 3, 6, 7, 18, 19, 22, 23] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[481]? = some (⟨245,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) from rfl))
private theorem rec12930 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 9, 10, 13, 14] : List ℕ)) (hp : parent ∈ ([1, 5] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[482]? = some (⟨245,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12947 (si parent : ℕ) (hs : si ∈ ([1, 5, 9, 13] : List ℕ)) (hp : parent ∈ ([0, 4] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,5,9,13],[0,4],881⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[499]? = some (⟨245,(-1),[1,5,9,13],[0,4],881⟩) from rfl))
private theorem rec12977 (si parent : ℕ) (hs : si ∈ ([9, 10, 13] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[529]? = some (⟨245,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0000_0016 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 0).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 0).take 16 = [⟨1,0,[⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,1,[⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,2,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,3,[⟨true,true,1⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,4,[⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,5,[⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,6,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,7,[⟨true,true,1⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,8,[⟨true,true,11⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,9,[⟨true,true,11⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,10,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,11,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,12,[⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,13,[⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,14,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,15,[⟨true,true,1⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12947 13 0 (by decide) (by decide)
  · left
    exact rec12930 13 1 (by decide) (by decide)
  · left
    exact rec12929 13 2 (by decide) (by decide)
  · left
    exact rec12929 13 3 (by decide) (by decide)
  · left
    exact rec12947 13 4 (by decide) (by decide)
  · left
    exact rec12930 13 5 (by decide) (by decide)
  · left
    exact rec12929 13 6 (by decide) (by decide)
  · left
    exact rec12929 13 7 (by decide) (by decide)
  · left
    exact rec12932 13 8 (by decide) (by decide)
  · left
    exact rec12932 13 9 (by decide) (by decide)
  · left
    exact rec12977 13 10 (by decide) (by decide)
  · left
    exact rec12977 13 11 (by decide) (by decide)
  · left
    exact rec12932 13 12 (by decide) (by decide)
  · left
    exact rec12932 13 13 (by decide) (by decide)
  · left
    exact rec12977 13 14 (by decide) (by decide)
  · left
    exact rec12977 13 15 (by decide) (by decide)
end Section14Coverage_13_6_p0_16

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0000_0016


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0016_0032
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p16_32
private theorem rec12929 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 9, 10, 13, 14] : List ℕ)) (hp : parent ∈ ([2, 3, 6, 7, 18, 19, 22, 23] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[481]? = some (⟨245,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12933 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([17, 21, 41, 45, 57, 61] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[485]? = some (⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩) from rfl))
private theorem rec12948 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([16, 20, 40, 44, 56, 60] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,5,13],[16,20,40,44,56,60],881⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[500]? = some (⟨245,(-1),[1,5,13],[16,20,40,44,56,60],881⟩) from rfl))
private theorem rec12977 (si parent : ℕ) (hs : si ∈ ([9, 10, 13] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[529]? = some (⟨245,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0016_0032 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 16).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 16).take 16 = [⟨1,16,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,17,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,18,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,19,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,20,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,21,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,22,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,23,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,24,[⟨true,true,11⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,25,[⟨true,true,11⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,26,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,27,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,28,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,29,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,30,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,31,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12948 13 16 (by decide) (by decide)
  · left
    exact rec12933 13 17 (by decide) (by decide)
  · left
    exact rec12929 13 18 (by decide) (by decide)
  · left
    exact rec12929 13 19 (by decide) (by decide)
  · left
    exact rec12948 13 20 (by decide) (by decide)
  · left
    exact rec12933 13 21 (by decide) (by decide)
  · left
    exact rec12929 13 22 (by decide) (by decide)
  · left
    exact rec12929 13 23 (by decide) (by decide)
  · left
    exact rec12932 13 24 (by decide) (by decide)
  · left
    exact rec12932 13 25 (by decide) (by decide)
  · left
    exact rec12977 13 26 (by decide) (by decide)
  · left
    exact rec12977 13 27 (by decide) (by decide)
  · left
    exact rec12932 13 28 (by decide) (by decide)
  · left
    exact rec12932 13 29 (by decide) (by decide)
  · left
    exact rec12977 13 30 (by decide) (by decide)
  · left
    exact rec12977 13 31 (by decide) (by decide)
end Section14Coverage_13_6_p16_32

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0016_0032


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0032_0048
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p32_48
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12933 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([17, 21, 41, 45, 57, 61] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[485]? = some (⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩) from rfl))
private theorem rec12948 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([16, 20, 40, 44, 56, 60] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,5,13],[16,20,40,44,56,60],881⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[500]? = some (⟨245,(-1),[1,5,13],[16,20,40,44,56,60],881⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0032_0048 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 32).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 32).take 16 = [⟨1,32,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,33,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,34,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,35,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,36,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,37,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,38,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,39,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,40,[⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,41,[⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,42,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,43,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,44,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,45,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,46,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,47,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12932 13 32 (by decide) (by decide)
  · left
    exact rec12932 13 33 (by decide) (by decide)
  · left
    exact rec12985 13 34 (by decide) (by decide)
  · left
    exact rec12985 13 35 (by decide) (by decide)
  · left
    exact rec12932 13 36 (by decide) (by decide)
  · left
    exact rec12932 13 37 (by decide) (by decide)
  · left
    exact rec12985 13 38 (by decide) (by decide)
  · left
    exact rec12985 13 39 (by decide) (by decide)
  · left
    exact rec12948 13 40 (by decide) (by decide)
  · left
    exact rec12933 13 41 (by decide) (by decide)
  · left
    exact rec12931 13 42 (by decide) (by decide)
  · left
    exact rec12931 13 43 (by decide) (by decide)
  · left
    exact rec12948 13 44 (by decide) (by decide)
  · left
    exact rec12933 13 45 (by decide) (by decide)
  · left
    exact rec12931 13 46 (by decide) (by decide)
  · left
    exact rec12931 13 47 (by decide) (by decide)
end Section14Coverage_13_6_p32_48

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0032_0048


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0048_0064
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p48_64
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12933 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([17, 21, 41, 45, 57, 61] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[485]? = some (⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩) from rfl))
private theorem rec12948 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([16, 20, 40, 44, 56, 60] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,5,13],[16,20,40,44,56,60],881⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[500]? = some (⟨245,(-1),[1,5,13],[16,20,40,44,56,60],881⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0048_0064 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 48).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 48).take 16 = [⟨1,48,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,49,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,50,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,51,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,52,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,53,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,54,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,55,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,56,[⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,57,[⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,58,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,59,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,60,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,61,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,62,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,63,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12932 13 48 (by decide) (by decide)
  · left
    exact rec12932 13 49 (by decide) (by decide)
  · left
    exact rec12985 13 50 (by decide) (by decide)
  · left
    exact rec12985 13 51 (by decide) (by decide)
  · left
    exact rec12932 13 52 (by decide) (by decide)
  · left
    exact rec12932 13 53 (by decide) (by decide)
  · left
    exact rec12985 13 54 (by decide) (by decide)
  · left
    exact rec12985 13 55 (by decide) (by decide)
  · left
    exact rec12948 13 56 (by decide) (by decide)
  · left
    exact rec12933 13 57 (by decide) (by decide)
  · left
    exact rec12931 13 58 (by decide) (by decide)
  · left
    exact rec12931 13 59 (by decide) (by decide)
  · left
    exact rec12948 13 60 (by decide) (by decide)
  · left
    exact rec12933 13 61 (by decide) (by decide)
  · left
    exact rec12931 13 62 (by decide) (by decide)
  · left
    exact rec12931 13 63 (by decide) (by decide)
end Section14Coverage_13_6_p48_64

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0048_0064


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0064_0080
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p64_80
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12934 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([64, 68, 80, 84, 104, 108, 120, 124] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[486]? = some (⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) from rfl))
private theorem rec12935 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([65, 69, 81, 85, 105, 109, 121, 125] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[487]? = some (⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0064_0080 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 64).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 64).take 16 = [⟨1,64,[⟨true,false,15⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,65,[⟨true,false,15⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,66,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,67,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,68,[⟨true,false,15⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,69,[⟨true,false,15⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,70,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,71,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,72,[⟨true,true,11⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,73,[⟨true,true,11⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,74,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,75,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,76,[⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,77,[⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,78,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,79,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12934 13 64 (by decide) (by decide)
  · left
    exact rec12935 13 65 (by decide) (by decide)
  · left
    exact rec12931 13 66 (by decide) (by decide)
  · left
    exact rec12931 13 67 (by decide) (by decide)
  · left
    exact rec12934 13 68 (by decide) (by decide)
  · left
    exact rec12935 13 69 (by decide) (by decide)
  · left
    exact rec12931 13 70 (by decide) (by decide)
  · left
    exact rec12931 13 71 (by decide) (by decide)
  · left
    exact rec12932 13 72 (by decide) (by decide)
  · left
    exact rec12932 13 73 (by decide) (by decide)
  · left
    exact rec12985 13 74 (by decide) (by decide)
  · left
    exact rec12985 13 75 (by decide) (by decide)
  · left
    exact rec12932 13 76 (by decide) (by decide)
  · left
    exact rec12932 13 77 (by decide) (by decide)
  · left
    exact rec12985 13 78 (by decide) (by decide)
  · left
    exact rec12985 13 79 (by decide) (by decide)
end Section14Coverage_13_6_p64_80

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0064_0080


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0080_0096
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p80_96
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12934 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([64, 68, 80, 84, 104, 108, 120, 124] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[486]? = some (⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) from rfl))
private theorem rec12935 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([65, 69, 81, 85, 105, 109, 121, 125] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[487]? = some (⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0080_0096 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 80).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 80).take 16 = [⟨1,80,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,81,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,82,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,83,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,84,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,85,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,86,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,87,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,88,[⟨true,true,11⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,89,[⟨true,true,11⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,90,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,91,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,92,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,93,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,94,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,95,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12934 13 80 (by decide) (by decide)
  · left
    exact rec12935 13 81 (by decide) (by decide)
  · left
    exact rec12931 13 82 (by decide) (by decide)
  · left
    exact rec12931 13 83 (by decide) (by decide)
  · left
    exact rec12934 13 84 (by decide) (by decide)
  · left
    exact rec12935 13 85 (by decide) (by decide)
  · left
    exact rec12931 13 86 (by decide) (by decide)
  · left
    exact rec12931 13 87 (by decide) (by decide)
  · left
    exact rec12932 13 88 (by decide) (by decide)
  · left
    exact rec12932 13 89 (by decide) (by decide)
  · left
    exact rec12985 13 90 (by decide) (by decide)
  · left
    exact rec12985 13 91 (by decide) (by decide)
  · left
    exact rec12932 13 92 (by decide) (by decide)
  · left
    exact rec12932 13 93 (by decide) (by decide)
  · left
    exact rec12985 13 94 (by decide) (by decide)
  · left
    exact rec12985 13 95 (by decide) (by decide)
end Section14Coverage_13_6_p80_96

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0080_0096


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0096_0112
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p96_112
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12934 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([64, 68, 80, 84, 104, 108, 120, 124] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[486]? = some (⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) from rfl))
private theorem rec12935 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([65, 69, 81, 85, 105, 109, 121, 125] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[487]? = some (⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0096_0112 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 96).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 96).take 16 = [⟨1,96,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,97,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,98,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,99,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,100,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,101,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,102,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,103,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,104,[⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,105,[⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,106,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,107,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨1,108,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,109,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,110,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,111,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12932 13 96 (by decide) (by decide)
  · left
    exact rec12932 13 97 (by decide) (by decide)
  · left
    exact rec12985 13 98 (by decide) (by decide)
  · left
    exact rec12985 13 99 (by decide) (by decide)
  · left
    exact rec12932 13 100 (by decide) (by decide)
  · left
    exact rec12932 13 101 (by decide) (by decide)
  · left
    exact rec12985 13 102 (by decide) (by decide)
  · left
    exact rec12985 13 103 (by decide) (by decide)
  · left
    exact rec12934 13 104 (by decide) (by decide)
  · left
    exact rec12935 13 105 (by decide) (by decide)
  · left
    exact rec12931 13 106 (by decide) (by decide)
  · left
    exact rec12931 13 107 (by decide) (by decide)
  · left
    exact rec12934 13 108 (by decide) (by decide)
  · left
    exact rec12935 13 109 (by decide) (by decide)
  · left
    exact rec12931 13 110 (by decide) (by decide)
  · left
    exact rec12931 13 111 (by decide) (by decide)
end Section14Coverage_13_6_p96_112

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0096_0112


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0112_0128
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p112_128
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12934 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([64, 68, 80, 84, 104, 108, 120, 124] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[486]? = some (⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) from rfl))
private theorem rec12935 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([65, 69, 81, 85, 105, 109, 121, 125] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[487]? = some (⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0112_0128 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 112).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 112).take 16 = [⟨1,112,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,113,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,114,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,115,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,116,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,117,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,118,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,119,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,120,[⟨true,true,11⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,121,[⟨true,true,11⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,122,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,123,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,124,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,125,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,126,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,127,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12932 13 112 (by decide) (by decide)
  · left
    exact rec12932 13 113 (by decide) (by decide)
  · left
    exact rec12985 13 114 (by decide) (by decide)
  · left
    exact rec12985 13 115 (by decide) (by decide)
  · left
    exact rec12932 13 116 (by decide) (by decide)
  · left
    exact rec12932 13 117 (by decide) (by decide)
  · left
    exact rec12985 13 118 (by decide) (by decide)
  · left
    exact rec12985 13 119 (by decide) (by decide)
  · left
    exact rec12934 13 120 (by decide) (by decide)
  · left
    exact rec12935 13 121 (by decide) (by decide)
  · left
    exact rec12931 13 122 (by decide) (by decide)
  · left
    exact rec12931 13 123 (by decide) (by decide)
  · left
    exact rec12934 13 124 (by decide) (by decide)
  · left
    exact rec12935 13 125 (by decide) (by decide)
  · left
    exact rec12931 13 126 (by decide) (by decide)
  · left
    exact rec12931 13 127 (by decide) (by decide)
end Section14Coverage_13_6_p112_128

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0112_0128


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0128_0144
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p128_144
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12936 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([130, 134] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[130,134],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[488]? = some (⟨245,(-1),[1,2,5,6,13,14],[130,134],884⟩) from rfl))
private theorem rec12945 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 135] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,13,14],[131,135],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[497]? = some (⟨245,(-1),[1,2,13,14],[131,135],884⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0128_0144 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 128).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 128).take 16 = [⟨1,128,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,129,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,130,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,131,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,132,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,133,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,134,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,135,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,136,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,137,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,138,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,139,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,140,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,141,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,142,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,143,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12931 13 128 (by decide) (by decide)
  · left
    exact rec12931 13 129 (by decide) (by decide)
  · left
    exact rec12936 13 130 (by decide) (by decide)
  · left
    exact rec12945 13 131 (by decide) (by decide)
  · left
    exact rec12931 13 132 (by decide) (by decide)
  · left
    exact rec12931 13 133 (by decide) (by decide)
  · left
    exact rec12936 13 134 (by decide) (by decide)
  · left
    exact rec12945 13 135 (by decide) (by decide)
  · left
    exact rec12985 13 136 (by decide) (by decide)
  · left
    exact rec12985 13 137 (by decide) (by decide)
  · left
    exact rec12932 13 138 (by decide) (by decide)
  · left
    exact rec12932 13 139 (by decide) (by decide)
  · left
    exact rec12985 13 140 (by decide) (by decide)
  · left
    exact rec12985 13 141 (by decide) (by decide)
  · left
    exact rec12932 13 142 (by decide) (by decide)
  · left
    exact rec12932 13 143 (by decide) (by decide)
end Section14Coverage_13_6_p128_144

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0128_0144


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0144_0160
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p144_160
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12937 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[146],885⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[489]? = some (⟨245,(-1),[1,2,5,6,13,14],[146],885⟩) from rfl))
private theorem rec12938 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 151, 171, 175, 187, 191] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[490]? = some (⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) from rfl))
private theorem rec12939 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[150],887⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[491]? = some (⟨245,(-1),[1,2,5,6,13,14],[150],887⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0144_0160 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 144).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 144).take 16 = [⟨1,144,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,145,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,146,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,147,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,148,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,149,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,150,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,151,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,152,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,153,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,154,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,155,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,156,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,157,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,158,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,159,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12931 13 144 (by decide) (by decide)
  · left
    exact rec12931 13 145 (by decide) (by decide)
  · left
    exact rec12937 13 146 (by decide) (by decide)
  · left
    exact rec12938 13 147 (by decide) (by decide)
  · left
    exact rec12931 13 148 (by decide) (by decide)
  · left
    exact rec12931 13 149 (by decide) (by decide)
  · left
    exact rec12939 13 150 (by decide) (by decide)
  · left
    exact rec12938 13 151 (by decide) (by decide)
  · left
    exact rec12985 13 152 (by decide) (by decide)
  · left
    exact rec12985 13 153 (by decide) (by decide)
  · left
    exact rec12932 13 154 (by decide) (by decide)
  · left
    exact rec12932 13 155 (by decide) (by decide)
  · left
    exact rec12985 13 156 (by decide) (by decide)
  · left
    exact rec12985 13 157 (by decide) (by decide)
  · left
    exact rec12932 13 158 (by decide) (by decide)
  · left
    exact rec12932 13 159 (by decide) (by decide)
end Section14Coverage_13_6_p144_160

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0144_0160


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0160_0176
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p160_176
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12938 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 151, 171, 175, 187, 191] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[490]? = some (⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) from rfl))
private theorem rec12940 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[174],908⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[492]? = some (⟨245,(-1),[1,2,5,6,13,14],[174],908⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
private theorem rec12987 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(0),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[539]? = some (⟨247,(0),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12989 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(1),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[541]? = some (⟨247,(1),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12991 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(2),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[543]? = some (⟨247,(2),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12993 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(3),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[545]? = some (⟨247,(3),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12995 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(4),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[547]? = some (⟨247,(4),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12997 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(5),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[549]? = some (⟨247,(5),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12999 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(6),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[551]? = some (⟨247,(6),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13001 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(7),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[553]? = some (⟨247,(7),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13003 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(8),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[555]? = some (⟨247,(8),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13005 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(9),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[557]? = some (⟨247,(9),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13007 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(10),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[559]? = some (⟨247,(10),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13009 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(11),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[561]? = some (⟨247,(11),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13011 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(12),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[563]? = some (⟨247,(12),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13013 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(13),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[565]? = some (⟨247,(13),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13015 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(14),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[567]? = some (⟨247,(14),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13017 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(15),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[569]? = some (⟨247,(15),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13019 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(16),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[571]? = some (⟨247,(16),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13021 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(17),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[573]? = some (⟨247,(17),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13023 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(18),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[575]? = some (⟨247,(18),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13025 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(19),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[577]? = some (⟨247,(19),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13027 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(20),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[579]? = some (⟨247,(20),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13029 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(21),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[581]? = some (⟨247,(21),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13031 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(22),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[583]? = some (⟨247,(22),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13033 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(23),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[585]? = some (⟨247,(23),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13035 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(24),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[587]? = some (⟨247,(24),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13037 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(0),[1,2,5,6,13,14],[170],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[589]? = some (⟨249,(0),[1,2,5,6,13,14],[170],10⟩) from rfl))
private theorem rec13039 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(1),[1,13],[170],11⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[591]? = some (⟨249,(1),[1,13],[170],11⟩) from rfl))
private theorem rec13042 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(2),[1,2,5,6,13,14],[170],888⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[594]? = some (⟨249,(2),[1,2,5,6,13,14],[170],888⟩) from rfl))
private theorem rec13044 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(3),[1,2,5,6,13,14],[170],889⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[596]? = some (⟨249,(3),[1,2,5,6,13,14],[170],889⟩) from rfl))
private theorem rec13046 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(4),[1,2,5,6,13,14],[170],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[598]? = some (⟨249,(4),[1,2,5,6,13,14],[170],890⟩) from rfl))
private theorem rec13048 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(5),[1,2,5,6,13,14],[170],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[600]? = some (⟨249,(5),[1,2,5,6,13,14],[170],10⟩) from rfl))
private theorem rec13050 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(6),[1,13],[170],11⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[602]? = some (⟨249,(6),[1,13],[170],11⟩) from rfl))
private theorem rec13053 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(7),[1,2,5,6,13,14],[170],888⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[605]? = some (⟨249,(7),[1,2,5,6,13,14],[170],888⟩) from rfl))
private theorem rec13055 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(8),[1,2,5,6,13,14],[170],889⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[607]? = some (⟨249,(8),[1,2,5,6,13,14],[170],889⟩) from rfl))
private theorem rec13057 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(9),[1,2,5,6,13,14],[170],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[609]? = some (⟨249,(9),[1,2,5,6,13,14],[170],890⟩) from rfl))
private theorem rec13059 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(10),[1,2,5,6,13,14],[170],18⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[611]? = some (⟨249,(10),[1,2,5,6,13,14],[170],18⟩) from rfl))
private theorem rec13061 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(11),[1,13],[170],19⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[613]? = some (⟨249,(11),[1,13],[170],19⟩) from rfl))
private theorem rec13064 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(12),[1,2,5,6,13,14],[170],891⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[616]? = some (⟨249,(12),[1,2,5,6,13,14],[170],891⟩) from rfl))
private theorem rec13066 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(13),[1,2,5,6,13,14],[170],891⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[618]? = some (⟨249,(13),[1,2,5,6,13,14],[170],891⟩) from rfl))
private theorem rec13068 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(14),[1,2,5,6,13,14],[170],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[620]? = some (⟨249,(14),[1,2,5,6,13,14],[170],890⟩) from rfl))
private theorem rec13070 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(15),[1,2,5,6,13,14],[170],21⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[622]? = some (⟨249,(15),[1,2,5,6,13,14],[170],21⟩) from rfl))
private theorem rec13072 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(16),[1,13],[170],22⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[624]? = some (⟨249,(16),[1,13],[170],22⟩) from rfl))
private theorem rec13075 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(17),[1,2,5,6,13,14],[170],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[627]? = some (⟨249,(17),[1,2,5,6,13,14],[170],892⟩) from rfl))
private theorem rec13077 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(18),[1,2,5,6,13,14],[170],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[629]? = some (⟨249,(18),[1,2,5,6,13,14],[170],892⟩) from rfl))
private theorem rec13079 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(19),[1,2,5,6,13,14],[170],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[631]? = some (⟨249,(19),[1,2,5,6,13,14],[170],892⟩) from rfl))
private theorem rec13081 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(20),[1,2,5,6,13,14],[170],24⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[633]? = some (⟨249,(20),[1,2,5,6,13,14],[170],24⟩) from rfl))
private theorem rec13083 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(21),[1,13],[170],25⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[635]? = some (⟨249,(21),[1,13],[170],25⟩) from rfl))
private theorem rec13086 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(22),[1,2,5,6,13,14],[170],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[638]? = some (⟨249,(22),[1,2,5,6,13,14],[170],893⟩) from rfl))
private theorem rec13088 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(23),[1,2,5,6,13,14],[170],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[640]? = some (⟨249,(23),[1,2,5,6,13,14],[170],893⟩) from rfl))
private theorem rec13090 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(24),[1,2,5,6,13,14],[170],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[642]? = some (⟨249,(24),[1,2,5,6,13,14],[170],893⟩) from rfl))
private theorem rec13092 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(0),[1,2,5,6,13,14],[170],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[644]? = some (⟨253,(0),[1,2,5,6,13,14],[170],884⟩) from rfl))
private theorem rec13096 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(1),[1,2,5,6,13,14],[170],894⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[648]? = some (⟨253,(1),[1,2,5,6,13,14],[170],894⟩) from rfl))
private theorem rec13100 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(2),[1,2,5,6,13,14],[170],895⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[652]? = some (⟨253,(2),[1,2,5,6,13,14],[170],895⟩) from rfl))
private theorem rec13104 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(3),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[656]? = some (⟨253,(3),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec13107 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(4),[1,2,5,6,13,14],[170],30⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[659]? = some (⟨253,(4),[1,2,5,6,13,14],[170],30⟩) from rfl))
private theorem rec13110 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(5),[1,2,5,6,13,14],[170],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[662]? = some (⟨253,(5),[1,2,5,6,13,14],[170],884⟩) from rfl))
private theorem rec13114 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(6),[1,2,5,6,13,14],[170],894⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[666]? = some (⟨253,(6),[1,2,5,6,13,14],[170],894⟩) from rfl))
private theorem rec13118 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(7),[1,2,5,6,13,14],[170],896⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[670]? = some (⟨253,(7),[1,2,5,6,13,14],[170],896⟩) from rfl))
private theorem rec13123 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(8),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[675]? = some (⟨253,(8),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec13126 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(9),[1,2,5,6,13,14],[170],32⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[678]? = some (⟨253,(9),[1,2,5,6,13,14],[170],32⟩) from rfl))
private theorem rec13129 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(10),[1,2,5,6,13,14],[170],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[681]? = some (⟨253,(10),[1,2,5,6,13,14],[170],84⟩) from rfl))
private theorem rec13132 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(11),[1,2,5,6,13,14],[170],897⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[684]? = some (⟨253,(11),[1,2,5,6,13,14],[170],897⟩) from rfl))
private theorem rec13135 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(12),[1,2,5,6,13,14],[170],898⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[687]? = some (⟨253,(12),[1,2,5,6,13,14],[170],898⟩) from rfl))
private theorem rec13138 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(13),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[690]? = some (⟨253,(13),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec13141 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(14),[1,2,5,6,13,14],[170],34⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[693]? = some (⟨253,(14),[1,2,5,6,13,14],[170],34⟩) from rfl))
private theorem rec13144 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(15),[1,2,5,6,13,14],[170],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[696]? = some (⟨253,(15),[1,2,5,6,13,14],[170],35⟩) from rfl))
private theorem rec13147 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(16),[1,2,5,6,13,14],[170],36⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[699]? = some (⟨253,(16),[1,2,5,6,13,14],[170],36⟩) from rfl))
private theorem rec13150 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(17),[1,2,5,6,13,14],[170],37⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[702]? = some (⟨253,(17),[1,2,5,6,13,14],[170],37⟩) from rfl))
private theorem rec13153 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(18),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[705]? = some (⟨253,(18),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec13156 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(19),[1,2,5,6,13,14],[170],37⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[708]? = some (⟨253,(19),[1,2,5,6,13,14],[170],37⟩) from rfl))
private theorem rec13159 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(20),[1,2,5,6,13,14],[170],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[711]? = some (⟨253,(20),[1,2,5,6,13,14],[170],38⟩) from rfl))
private theorem rec13162 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(21),[1,2,5,6,13,14],[170],39⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[714]? = some (⟨253,(21),[1,2,5,6,13,14],[170],39⟩) from rfl))
private theorem rec13165 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(22),[1,2,5,6,13,14],[170],40⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[717]? = some (⟨253,(22),[1,2,5,6,13,14],[170],40⟩) from rfl))
private theorem rec13168 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(23),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[720]? = some (⟨253,(23),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec13171 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(24),[1,2,5,6,13,14],[170],40⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[723]? = some (⟨253,(24),[1,2,5,6,13,14],[170],40⟩) from rfl))
private theorem rec13225 (si parent : ℕ) (hs : si ∈ ([6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(5),[6,13],[170],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[777]? = some (⟨258,(5),[6,13],[170],105⟩) from rfl))
private theorem rec13226 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(7),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[778]? = some (⟨258,(7),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13227 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(8),[1,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[779]? = some (⟨258,(8),[1,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13230 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(9),[5,6,13,14],[170],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[782]? = some (⟨258,(9),[5,6,13,14],[170],143⟩) from rfl))
private theorem rec13232 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(15),[5,13],[170],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[784]? = some (⟨258,(15),[5,13],[170],48⟩) from rfl))
private theorem rec13233 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(16),[1,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[785]? = some (⟨258,(16),[1,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13235 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(17),[1,2,5,6,13,14],[170],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[787]? = some (⟨258,(17),[1,2,5,6,13,14],[170],48⟩) from rfl))
private theorem rec13236 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(19),[1,13],[170],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[788]? = some (⟨258,(19),[1,13],[170],48⟩) from rfl))
private theorem rec16578 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(0),[13,14],[170],1729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[370]? = some (⟨643,(0),[13,14],[170],1729⟩) from rfl))
private theorem rec16580 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(1),[13,14],[170],1729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[372]? = some (⟨643,(1),[13,14],[170],1729⟩) from rfl))
private theorem rec16582 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(2),[13,14],[170],1730⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[374]? = some (⟨643,(2),[13,14],[170],1730⟩) from rfl))
private theorem rec16584 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(3),[13,14],[170],1730⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[376]? = some (⟨643,(3),[13,14],[170],1730⟩) from rfl))
private theorem rec16586 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(4),[13,14],[170],1729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[378]? = some (⟨643,(4),[13,14],[170],1729⟩) from rfl))
private theorem rec16588 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(5),[13,14],[170],1729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[380]? = some (⟨643,(5),[13,14],[170],1729⟩) from rfl))
private theorem rec16590 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(6),[13,14],[170],1731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[382]? = some (⟨643,(6),[13,14],[170],1731⟩) from rfl))
private theorem rec16592 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(7),[13,14],[170],1731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[384]? = some (⟨643,(7),[13,14],[170],1731⟩) from rfl))
private theorem rec16594 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(8),[13,14],[170],905⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[386]? = some (⟨643,(8),[13,14],[170],905⟩) from rfl))
private theorem rec16596 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(9),[13,14],[170],905⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[388]? = some (⟨643,(9),[13,14],[170],905⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0160_0176 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 160).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 160).take 16 = [⟨1,160,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,161,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,162,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,163,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,164,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,165,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,166,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,167,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,168,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,169,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,170,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨1,171,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨1,172,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,173,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,174,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,175,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12985 13 160 (by decide) (by decide)
  · left
    exact rec12985 13 161 (by decide) (by decide)
  · left
    exact rec12932 13 162 (by decide) (by decide)
  · left
    exact rec12932 13 163 (by decide) (by decide)
  · left
    exact rec12985 13 164 (by decide) (by decide)
  · left
    exact rec12985 13 165 (by decide) (by decide)
  · left
    exact rec12932 13 166 (by decide) (by decide)
  · left
    exact rec12932 13 167 (by decide) (by decide)
  · left
    exact rec12931 13 168 (by decide) (by decide)
  · left
    exact rec12931 13 169 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 246)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 247)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12987 13 170 (by decide) (by decide)
      · right
        exact rec12989 13 170 (by decide) (by decide)
      · right
        exact rec12991 13 170 (by decide) (by decide)
      · right
        exact rec12993 13 170 (by decide) (by decide)
      · right
        exact rec12995 13 170 (by decide) (by decide)
      · right
        exact rec12997 13 170 (by decide) (by decide)
      · right
        exact rec12999 13 170 (by decide) (by decide)
      · right
        exact rec13001 13 170 (by decide) (by decide)
      · right
        exact rec13003 13 170 (by decide) (by decide)
      · right
        exact rec13005 13 170 (by decide) (by decide)
      · right
        exact rec13007 13 170 (by decide) (by decide)
      · right
        exact rec13009 13 170 (by decide) (by decide)
      · right
        exact rec13011 13 170 (by decide) (by decide)
      · right
        exact rec13013 13 170 (by decide) (by decide)
      · right
        exact rec13015 13 170 (by decide) (by decide)
      · right
        exact rec13017 13 170 (by decide) (by decide)
      · right
        exact rec13019 13 170 (by decide) (by decide)
      · right
        exact rec13021 13 170 (by decide) (by decide)
      · right
        exact rec13023 13 170 (by decide) (by decide)
      · right
        exact rec13025 13 170 (by decide) (by decide)
      · right
        exact rec13027 13 170 (by decide) (by decide)
      · right
        exact rec13029 13 170 (by decide) (by decide)
      · right
        exact rec13031 13 170 (by decide) (by decide)
      · right
        exact rec13033 13 170 (by decide) (by decide)
      · right
        exact rec13035 13 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 248)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 249)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13037 13 170 (by decide) (by decide)
      · right
        exact rec13039 13 170 (by decide) (by decide)
      · right
        exact rec13042 13 170 (by decide) (by decide)
      · right
        exact rec13044 13 170 (by decide) (by decide)
      · right
        exact rec13046 13 170 (by decide) (by decide)
      · right
        exact rec13048 13 170 (by decide) (by decide)
      · right
        exact rec13050 13 170 (by decide) (by decide)
      · right
        exact rec13053 13 170 (by decide) (by decide)
      · right
        exact rec13055 13 170 (by decide) (by decide)
      · right
        exact rec13057 13 170 (by decide) (by decide)
      · right
        exact rec13059 13 170 (by decide) (by decide)
      · right
        exact rec13061 13 170 (by decide) (by decide)
      · right
        exact rec13064 13 170 (by decide) (by decide)
      · right
        exact rec13066 13 170 (by decide) (by decide)
      · right
        exact rec13068 13 170 (by decide) (by decide)
      · right
        exact rec13070 13 170 (by decide) (by decide)
      · right
        exact rec13072 13 170 (by decide) (by decide)
      · right
        exact rec13075 13 170 (by decide) (by decide)
      · right
        exact rec13077 13 170 (by decide) (by decide)
      · right
        exact rec13079 13 170 (by decide) (by decide)
      · right
        exact rec13081 13 170 (by decide) (by decide)
      · right
        exact rec13083 13 170 (by decide) (by decide)
      · right
        exact rec13086 13 170 (by decide) (by decide)
      · right
        exact rec13088 13 170 (by decide) (by decide)
      · right
        exact rec13090 13 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 250)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 641)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 252)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 253)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13092 13 170 (by decide) (by decide)
      · right
        exact rec13096 13 170 (by decide) (by decide)
      · right
        exact rec13100 13 170 (by decide) (by decide)
      · right
        exact rec13104 13 170 (by decide) (by decide)
      · right
        exact rec13107 13 170 (by decide) (by decide)
      · right
        exact rec13110 13 170 (by decide) (by decide)
      · right
        exact rec13114 13 170 (by decide) (by decide)
      · right
        exact rec13118 13 170 (by decide) (by decide)
      · right
        exact rec13123 13 170 (by decide) (by decide)
      · right
        exact rec13126 13 170 (by decide) (by decide)
      · right
        exact rec13129 13 170 (by decide) (by decide)
      · right
        exact rec13132 13 170 (by decide) (by decide)
      · right
        exact rec13135 13 170 (by decide) (by decide)
      · right
        exact rec13138 13 170 (by decide) (by decide)
      · right
        exact rec13141 13 170 (by decide) (by decide)
      · right
        exact rec13144 13 170 (by decide) (by decide)
      · right
        exact rec13147 13 170 (by decide) (by decide)
      · right
        exact rec13150 13 170 (by decide) (by decide)
      · right
        exact rec13153 13 170 (by decide) (by decide)
      · right
        exact rec13156 13 170 (by decide) (by decide)
      · right
        exact rec13159 13 170 (by decide) (by decide)
      · right
        exact rec13162 13 170 (by decide) (by decide)
      · right
        exact rec13165 13 170 (by decide) (by decide)
      · right
        exact rec13168 13 170 (by decide) (by decide)
      · right
        exact rec13171 13 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 642)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 643)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16578 13 170 (by decide) (by decide)
      · right
        exact rec16580 13 170 (by decide) (by decide)
      · right
        exact rec16582 13 170 (by decide) (by decide)
      · right
        exact rec16584 13 170 (by decide) (by decide)
      · right
        exact rec16586 13 170 (by decide) (by decide)
      · right
        exact rec16588 13 170 (by decide) (by decide)
      · right
        exact rec16590 13 170 (by decide) (by decide)
      · right
        exact rec16592 13 170 (by decide) (by decide)
      · right
        exact rec16594 13 170 (by decide) (by decide)
      · right
        exact rec16596 13 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 644)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 257)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 258)).length = 20 := by decide +kernel
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
        exact rec13225 13 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec13226 13 170 (by decide) (by decide)
      · right
        exact rec13227 13 170 (by decide) (by decide)
      · right
        exact rec13230 13 170 (by decide) (by decide)
      · left
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
        exact rec13232 13 170 (by decide) (by decide)
      · right
        exact rec13233 13 170 (by decide) (by decide)
      · right
        exact rec13235 13 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec13236 13 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 645)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
  · left
    exact rec12938 13 171 (by decide) (by decide)
  · left
    exact rec12931 13 172 (by decide) (by decide)
  · left
    exact rec12931 13 173 (by decide) (by decide)
  · left
    exact rec12940 13 174 (by decide) (by decide)
  · left
    exact rec12938 13 175 (by decide) (by decide)
end Section14Coverage_13_6_p160_176

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0160_0176


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0176_0192
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p176_192
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12938 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 151, 171, 175, 187, 191] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[490]? = some (⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) from rfl))
private theorem rec12941 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[186],909⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[493]? = some (⟨245,(-1),[1,2,5,6,13,14],[186],909⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
private theorem rec12986 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[190],908⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[538]? = some (⟨245,(-1),[13],[190],908⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0176_0192 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 176).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 176).take 16 = [⟨1,176,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,177,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,178,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,179,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,180,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,181,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,182,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,183,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,184,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,185,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,186,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,187,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,188,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,189,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,190,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,191,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12985 13 176 (by decide) (by decide)
  · left
    exact rec12985 13 177 (by decide) (by decide)
  · left
    exact rec12932 13 178 (by decide) (by decide)
  · left
    exact rec12932 13 179 (by decide) (by decide)
  · left
    exact rec12985 13 180 (by decide) (by decide)
  · left
    exact rec12985 13 181 (by decide) (by decide)
  · left
    exact rec12932 13 182 (by decide) (by decide)
  · left
    exact rec12932 13 183 (by decide) (by decide)
  · left
    exact rec12931 13 184 (by decide) (by decide)
  · left
    exact rec12931 13 185 (by decide) (by decide)
  · left
    exact rec12941 13 186 (by decide) (by decide)
  · left
    exact rec12938 13 187 (by decide) (by decide)
  · left
    exact rec12931 13 188 (by decide) (by decide)
  · left
    exact rec12931 13 189 (by decide) (by decide)
  · left
    exact rec12986 13 190 (by decide) (by decide)
  · left
    exact rec12938 13 191 (by decide) (by decide)
end Section14Coverage_13_6_p176_192

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0176_0192


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0192_0208
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p192_208
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12946 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([194, 198] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,5,6,13],[194,198],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[498]? = some (⟨245,(-1),[1,5,6,13],[194,198],910⟩) from rfl))
private theorem rec12949 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([195, 199, 211, 215, 235, 239, 251, 255] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[501]? = some (⟨245,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0192_0208 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 192).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 192).take 16 = [⟨1,192,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,193,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,194,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,19⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,195,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,196,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,197,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,198,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,19⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,199,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,200,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,201,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,202,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,203,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,204,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,205,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,206,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,207,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12931 13 192 (by decide) (by decide)
  · left
    exact rec12931 13 193 (by decide) (by decide)
  · left
    exact rec12946 13 194 (by decide) (by decide)
  · left
    exact rec12949 13 195 (by decide) (by decide)
  · left
    exact rec12931 13 196 (by decide) (by decide)
  · left
    exact rec12931 13 197 (by decide) (by decide)
  · left
    exact rec12946 13 198 (by decide) (by decide)
  · left
    exact rec12949 13 199 (by decide) (by decide)
  · left
    exact rec12985 13 200 (by decide) (by decide)
  · left
    exact rec12985 13 201 (by decide) (by decide)
  · left
    exact rec12932 13 202 (by decide) (by decide)
  · left
    exact rec12932 13 203 (by decide) (by decide)
  · left
    exact rec12985 13 204 (by decide) (by decide)
  · left
    exact rec12985 13 205 (by decide) (by decide)
  · left
    exact rec12932 13 206 (by decide) (by decide)
  · left
    exact rec12932 13 207 (by decide) (by decide)
end Section14Coverage_13_6_p192_208

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0192_0208


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0208_0224
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p208_224
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12942 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([210, 214, 234, 238, 250, 254] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[494]? = some (⟨245,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) from rfl))
private theorem rec12949 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([195, 199, 211, 215, 235, 239, 251, 255] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[501]? = some (⟨245,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0208_0224 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 208).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 208).take 16 = [⟨1,208,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,209,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,210,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,211,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,212,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,213,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,214,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,215,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,216,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,217,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,218,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,219,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,220,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,221,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,222,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,223,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12931 13 208 (by decide) (by decide)
  · left
    exact rec12931 13 209 (by decide) (by decide)
  · left
    exact rec12942 13 210 (by decide) (by decide)
  · left
    exact rec12949 13 211 (by decide) (by decide)
  · left
    exact rec12931 13 212 (by decide) (by decide)
  · left
    exact rec12931 13 213 (by decide) (by decide)
  · left
    exact rec12942 13 214 (by decide) (by decide)
  · left
    exact rec12949 13 215 (by decide) (by decide)
  · left
    exact rec12985 13 216 (by decide) (by decide)
  · left
    exact rec12985 13 217 (by decide) (by decide)
  · left
    exact rec12932 13 218 (by decide) (by decide)
  · left
    exact rec12932 13 219 (by decide) (by decide)
  · left
    exact rec12985 13 220 (by decide) (by decide)
  · left
    exact rec12985 13 221 (by decide) (by decide)
  · left
    exact rec12932 13 222 (by decide) (by decide)
  · left
    exact rec12932 13 223 (by decide) (by decide)
end Section14Coverage_13_6_p208_224

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0208_0224


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0224_0240
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p224_240
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12942 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([210, 214, 234, 238, 250, 254] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[494]? = some (⟨245,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) from rfl))
private theorem rec12949 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([195, 199, 211, 215, 235, 239, 251, 255] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[501]? = some (⟨245,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0224_0240 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 224).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 224).take 16 = [⟨1,224,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,225,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,226,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,227,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,228,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,229,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,230,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,231,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,232,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,233,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,234,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,235,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,236,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,237,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,238,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,239,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec12985 13 224 (by decide) (by decide)
  · left
    exact rec12985 13 225 (by decide) (by decide)
  · left
    exact rec12932 13 226 (by decide) (by decide)
  · left
    exact rec12932 13 227 (by decide) (by decide)
  · left
    exact rec12985 13 228 (by decide) (by decide)
  · left
    exact rec12985 13 229 (by decide) (by decide)
  · left
    exact rec12932 13 230 (by decide) (by decide)
  · left
    exact rec12932 13 231 (by decide) (by decide)
  · left
    exact rec12931 13 232 (by decide) (by decide)
  · left
    exact rec12931 13 233 (by decide) (by decide)
  · left
    exact rec12942 13 234 (by decide) (by decide)
  · left
    exact rec12949 13 235 (by decide) (by decide)
  · left
    exact rec12931 13 236 (by decide) (by decide)
  · left
    exact rec12931 13 237 (by decide) (by decide)
  · left
    exact rec12942 13 238 (by decide) (by decide)
  · left
    exact rec12949 13 239 (by decide) (by decide)
end Section14Coverage_13_6_p224_240

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0224_0240


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0240_0256
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_13_6_p240_256
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12942 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([210, 214, 234, 238, 250, 254] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[494]? = some (⟨245,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) from rfl))
private theorem rec12949 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([195, 199, 211, 215, 235, 239, 251, 255] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[501]? = some (⟨245,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) from rfl))
private theorem rec12985 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[537]? = some (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0013_coverage0006_parents_0240_0256 : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 240).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec12985 13 240 (by decide) (by decide)
  · left
    exact rec12985 13 241 (by decide) (by decide)
  · left
    exact rec12932 13 242 (by decide) (by decide)
  · left
    exact rec12932 13 243 (by decide) (by decide)
  · left
    exact rec12985 13 244 (by decide) (by decide)
  · left
    exact rec12985 13 245 (by decide) (by decide)
  · left
    exact rec12932 13 246 (by decide) (by decide)
  · left
    exact rec12932 13 247 (by decide) (by decide)
  · left
    exact rec12931 13 248 (by decide) (by decide)
  · left
    exact rec12931 13 249 (by decide) (by decide)
  · left
    exact rec12942 13 250 (by decide) (by decide)
  · left
    exact rec12949 13 251 (by decide) (by decide)
  · left
    exact rec12931 13 252 (by decide) (by decide)
  · left
    exact rec12931 13 253 (by decide) (by decide)
  · left
    exact rec12942 13 254 (by decide) (by decide)
  · left
    exact rec12949 13 255 (by decide) (by decide)
end Section14Coverage_13_6_p240_256

end WorkReverseInterface_Freiman_workReverse20260919_s0013_coverage0006_parents_0240_0256

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

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 6).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 13), section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  intro pl hpl
  let xs := section14Parents section14Catalog (section14State section14Catalog 13)
  let P := fun b : Section14Parent => section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j
  have h256 : ∀ x ∈ xs.drop 256, P x := by
    apply all_empty P _
    rfl
  have h240 : ∀ x ∈ xs.drop 240, P x := by
    apply all_of_chunks P xs 240 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0240_0256 pl hpl)
    exact h256
  have h224 : ∀ x ∈ xs.drop 224, P x := by
    apply all_of_chunks P xs 224 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0224_0240 pl hpl)
    exact h240
  have h208 : ∀ x ∈ xs.drop 208, P x := by
    apply all_of_chunks P xs 208 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0208_0224 pl hpl)
    exact h224
  have h192 : ∀ x ∈ xs.drop 192, P x := by
    apply all_of_chunks P xs 192 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0192_0208 pl hpl)
    exact h208
  have h176 : ∀ x ∈ xs.drop 176, P x := by
    apply all_of_chunks P xs 176 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0176_0192 pl hpl)
    exact h192
  have h160 : ∀ x ∈ xs.drop 160, P x := by
    apply all_of_chunks P xs 160 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0160_0176 pl hpl)
    exact h176
  have h144 : ∀ x ∈ xs.drop 144, P x := by
    apply all_of_chunks P xs 144 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0144_0160 pl hpl)
    exact h160
  have h128 : ∀ x ∈ xs.drop 128, P x := by
    apply all_of_chunks P xs 128 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0128_0144 pl hpl)
    exact h144
  have h112 : ∀ x ∈ xs.drop 112, P x := by
    apply all_of_chunks P xs 112 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0112_0128 pl hpl)
    exact h128
  have h96 : ∀ x ∈ xs.drop 96, P x := by
    apply all_of_chunks P xs 96 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0096_0112 pl hpl)
    exact h112
  have h80 : ∀ x ∈ xs.drop 80, P x := by
    apply all_of_chunks P xs 80 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0080_0096 pl hpl)
    exact h96
  have h64 : ∀ x ∈ xs.drop 64, P x := by
    apply all_of_chunks P xs 64 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0064_0080 pl hpl)
    exact h80
  have h48 : ∀ x ∈ xs.drop 48, P x := by
    apply all_of_chunks P xs 48 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0048_0064 pl hpl)
    exact h64
  have h32 : ∀ x ∈ xs.drop 32, P x := by
    apply all_of_chunks P xs 32 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0032_0048 pl hpl)
    exact h48
  have h16 : ∀ x ∈ xs.drop 16, P x := by
    apply all_of_chunks P xs 16 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0016_0032 pl hpl)
    exact h32
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 16 (Freiman.workReverse20260919_s0013_coverage0006_parents_0000_0016 pl hpl)
    exact h16
  simpa only [List.drop_zero] using h0

#print axioms solution
