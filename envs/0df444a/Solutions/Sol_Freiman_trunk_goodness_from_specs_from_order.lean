-- Prove2me | solution 1 for Freiman.trunk_goodness_from_specs_from_order
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T12:44:49.74209+00:00
-- url     : https://prove2.me/submissions/05607f9c-20c1-4f81-8d45-6b36abf704aa

import Definitions.Def_Freiman_trunkGeometry
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Mathlib.Tactic

open Freiman
namespace Goodness15

private theorem goodness (ho : ∀ w : LowerPair, lowerEndpoint w false < lowerEndpoint w true)
    (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp) :
    ∀ l ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels, lowerStrictGood (lowerChild p l) := by
  classical
  intro l hl
  let w := section14LabelWords l
  have hmem (sp : Section14Spec)
      (hi : sp ∈ (⟨w,true,w,false,false,[]⟩ :: (section14NormalCases w).flatMap fun (wide,norm) =>
        let one := lowerHistorySet w wide (lowerHistoryPick w wide ++ [1])
        let two := lowerHistorySet w wide (lowerHistoryPick w wide ++ [2])
        [⟨one,true,two,false,true,[norm]⟩,⟨two,true,one,false,true,[norm]⟩])) :
      sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi) := by
    unfold trunkSpecs
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨l,hl,hi⟩
  have hspec := hs
  have hf12 :
      trunkHolds [⟨false, false, lowerHistoryWH w⟩]
          (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) →
        trunkSpecLocalEndpoint p (lowerHistorySet w false (lowerHistoryPick w false ++ [2])) false false <
          trunkSpecLocalEndpoint p (lowerHistorySet w false (lowerHistoryPick w false ++ [1])) true false := by
    simpa [trunkSpecHolds, trunkSpecIncoming] using
      hspec ⟨lowerHistorySet w false (lowerHistoryPick w false ++ [1]), true,
        lowerHistorySet w false (lowerHistoryPick w false ++ [2]), false, true,
        [⟨false, false, lowerHistoryWH w⟩]⟩ (by
          apply hmem
          simp [section14NormalCases,w])
  have hf21 :
      trunkHolds [⟨false, false, lowerHistoryWH w⟩]
          (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) →
        trunkSpecLocalEndpoint p (lowerHistorySet w false (lowerHistoryPick w false ++ [1])) false false <
          trunkSpecLocalEndpoint p (lowerHistorySet w false (lowerHistoryPick w false ++ [2])) true false := by
    simpa [trunkSpecHolds, trunkSpecIncoming] using
      hspec ⟨lowerHistorySet w false (lowerHistoryPick w false ++ [2]), true,
        lowerHistorySet w false (lowerHistoryPick w false ++ [1]), false, true,
        [⟨false, false, lowerHistoryWH w⟩]⟩ (by
          apply hmem
          simp [section14NormalCases,w])
  have ht12 :
      trunkHolds [⟨true, true, lowerHistoryWH w⟩]
          (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) →
        trunkSpecLocalEndpoint p (lowerHistorySet w true (lowerHistoryPick w true ++ [2])) false true <
          trunkSpecLocalEndpoint p (lowerHistorySet w true (lowerHistoryPick w true ++ [1])) true true := by
    simpa [trunkSpecHolds, trunkSpecIncoming] using
      hspec ⟨lowerHistorySet w true (lowerHistoryPick w true ++ [1]), true,
        lowerHistorySet w true (lowerHistoryPick w true ++ [2]), false, true,
        [⟨true, true, lowerHistoryWH w⟩]⟩ (by
          apply hmem
          simp [section14NormalCases,w])
  have ht21 :
      trunkHolds [⟨true, true, lowerHistoryWH w⟩]
          (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) →
        trunkSpecLocalEndpoint p (lowerHistorySet w true (lowerHistoryPick w true ++ [1])) false true <
          trunkSpecLocalEndpoint p (lowerHistorySet w true (lowerHistoryPick w true ++ [2])) true true := by
    simpa [trunkSpecHolds, trunkSpecIncoming] using
      hspec ⟨lowerHistorySet w true (lowerHistoryPick w true ++ [2]), true,
        lowerHistorySet w true (lowerHistoryPick w true ++ [1]), false, true,
        [⟨true, true, lowerHistoryWH w⟩]⟩ (by
          apply hmem
          simp [section14NormalCases,w])
  let Z := lowerNormalize p
  have hc : lowerChild p l = (Z.1 ++ w.1, Z.2 ++ w.2) := by
    simp [lowerChild, w, section14LabelWords, Z]
  by_cases hw : lowerWidth (Z.2 ++ w.2) ≤ lowerWidth (Z.1 ++ w.1)
  · have hn : trunkHolds [⟨false, false, lowerHistoryWH w⟩]
        (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) := by
      have ht := (lowerHistory_width_threshold Z w).1.mp hw
      simpa [lowerHistoryAtBase, lowerHistoryConditions, trunkHolds,
        Z] using ht
    have ha := hf12 hn
    have hb := hf21 hn
    have hca : lowerChild (lowerChild p l) ([1], []) =
        (Z.1 ++ w.1 ++ [1], Z.2 ++ w.2) := by
      rw [hc]
      simp [lowerChild, lowerNormalize, hw]
    have hcb : lowerChild (lowerChild p l) ([2], []) =
        (Z.1 ++ w.1 ++ [2], Z.2 ++ w.2) := by
      rw [hc]
      simp [lowerChild, lowerNormalize, hw]
    have hoa := ho (Z.1 ++ w.1 ++ [1], Z.2 ++ w.2)
    have hob := ho (Z.1 ++ w.1 ++ [2], Z.2 ++ w.2)
    rw [lowerStrictGood, hca, hcb]
    simp only [max_lt_iff, lt_min_iff]
    by_cases he : Z.1.length % 2 = 0
    · simp [trunkSpecLocalEndpoint, lowerHistoryOrient, lowerHistoryAppend, Z, w, he, lowerHistorySet, lowerHistoryPick] at ha hb
      exact ⟨⟨hoa, by simpa [Z, w, List.append_assoc] using ha⟩,
        ⟨by simpa [Z, w, List.append_assoc] using hb, hob⟩⟩
    · simp [trunkSpecLocalEndpoint, lowerHistoryOrient, lowerHistoryAppend, Z, w, he, lowerHistorySet, lowerHistoryPick] at ha hb
      exact ⟨⟨hoa, by simpa [Z, w, List.append_assoc] using hb⟩,
        ⟨by simpa [Z, w, List.append_assoc] using ha, hob⟩⟩
  · have hw' : lowerWidth (Z.1 ++ w.1) < lowerWidth (Z.2 ++ w.2) := lt_of_not_ge hw
    have hn : trunkHolds [⟨true, true, lowerHistoryWH w⟩]
        (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) := by
      have hn0 : ¬ trunkHolds [⟨false, false, lowerHistoryWH w⟩]
          (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) := by
        intro ht
        apply hw
        have hw0 := (lowerHistory_width_threshold Z w).1.mpr (by
          simpa [lowerHistoryAtBase, lowerHistoryConditions, trunkHolds,
            Z] using ht)
        exact hw0
      simpa [trunkHolds, certBoundHolds] using hn0
    have ha := ht12 hn
    have hb := ht21 hn
    have hca : lowerChild (lowerChild p l) ([1], []) =
        (Z.2 ++ w.2 ++ [1], Z.1 ++ w.1) := by
      rw [hc]
      simp [lowerChild, lowerNormalize, hw, hw']
    have hcb : lowerChild (lowerChild p l) ([2], []) =
        (Z.2 ++ w.2 ++ [2], Z.1 ++ w.1) := by
      rw [hc]
      simp [lowerChild, lowerNormalize, hw, hw']
    have hoa := ho (Z.2 ++ w.2 ++ [1], Z.1 ++ w.1)
    have hob := ho (Z.2 ++ w.2 ++ [2], Z.1 ++ w.1)
    rw [lowerStrictGood, hca, hcb]
    simp only [max_lt_iff, lt_min_iff]
    by_cases he : Z.1.length % 2 = 0
    · simp [trunkSpecLocalEndpoint, lowerHistoryOrient, lowerHistoryAppend, Z, w, he,
        lowerHistorySet, lowerHistoryPick] at ha hb
      exact ⟨⟨hoa, by simpa [Z, w, List.append_assoc] using ha⟩,
        ⟨by simpa [Z, w, List.append_assoc] using hb, hob⟩⟩
    · simp [trunkSpecLocalEndpoint, lowerHistoryOrient, lowerHistoryAppend, Z, w, he,
        lowerHistorySet, lowerHistoryPick] at ha hb
      exact ⟨⟨hoa, by simpa [Z, w, List.append_assoc] using hb⟩,
        ⟨by simpa [Z, w, List.append_assoc] using ha, hob⟩⟩

end Goodness15

theorem solution (ho : ∀ w : LowerPair, lowerEndpoint w false < lowerEndpoint w true)
    (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp) :
    ∀ l ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels, lowerStrictGood (lowerChild p l) := by
  exact Goodness15.goodness ho p k pi par hm hs

#print axioms solution
