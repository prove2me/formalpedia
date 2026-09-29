-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_child_goodness_from_alignment
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:36:57.438354+00:00
-- url     : https://prove2.me/submissions/f539b52f-21d6-4dda-8bdc-593aea3c5143

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic.Linarith

open Freiman

theorem solution (p : LowerPair) (l : LowerLabel) (hw : LowerHistoryWidthLaw)
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true)
    (halign : lowerEarlyTerminalForkAlignment p l) (h : ∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) : lowerGood (lowerChild p l) := by
  -- pick the normalization case that actually holds
  obtain ⟨wide, norm, hmem, hnorm⟩ : ∃ wide norm, (wide, norm) ∈ section14NormalCases (section14LabelWords l) ∧
      lowerEarlyTerminalAt p [norm] := by
    by_cases hq : lowerEarlyTerminalQ p ≤ certThresholdVal (lowerHistoryWH (section14LabelWords l))
        (lowerEarlyTerminalR p) (lowerEarlyTerminalS p)
    · refine ⟨false, ⟨false,false,lowerHistoryWH (section14LabelWords l)⟩, by simp [section14NormalCases], ?_⟩
      intro b hb
      rw [List.mem_singleton] at hb
      subst hb
      simp only [certBoundHolds, Bool.false_eq_true, ↓reduceIte]
      exact hq
    · refine ⟨true, ⟨true,true,lowerHistoryWH (section14LabelWords l)⟩, by simp [section14NormalCases], ?_⟩
      intro b hb
      rw [List.mem_singleton] at hb
      subst hb
      simp only [certBoundHolds, ↓reduceIte]
      exact lt_of_not_ge hq

  set one := lowerHistorySet (section14LabelWords l) wide (lowerHistoryPick (section14LabelWords l) wide ++ [1]) with hone
  set two := lowerHistorySet (section14LabelWords l) wide (lowerHistoryPick (section14LabelWords l) wide ++ [2]) with htwo
  have hreq1 : ([norm], LowerEarlyTerminalKind.compare one true two false true) ∈
      lowerEarlyTerminalGoodRequirements [] l := by
    unfold lowerEarlyTerminalGoodRequirements
    exact List.mem_flatMap.2 ⟨(wide, norm), hmem, by simp [hone, htwo]⟩
  have hreq2 : ([norm], LowerEarlyTerminalKind.compare two true one false true) ∈
      lowerEarlyTerminalGoodRequirements [] l := by
    unfold lowerEarlyTerminalGoodRequirements
    exact List.mem_flatMap.2 ⟨(wide, norm), hmem, by simp [hone, htwo]⟩
  have k1 := h _ hreq1 hnorm
  have k2 := h _ hreq2 hnorm
  have key : ∀ (w' : LowerPair) (u : Bool), lowerEarlyTerminalEndpoint p w' u =
      (if lowerHistoryCommonOdd (lowerNormalize p) ⟨([],[]),(false,false)⟩ then -1 else 1) *
        lowerEndpoint (lowerHistoryAppend (lowerNormalize p) w')
          (u.xor (lowerHistoryCommonOdd (lowerNormalize p) ⟨([],[]),(false,false)⟩)) := by
    intro w' u
    rfl
  simp only [lowerEarlyTerminalKindHolds, ↓reduceIte, key] at k1 k2
  have hcross : lowerEndpoint (lowerHistoryAppend (lowerNormalize p) two) false <
        lowerEndpoint (lowerHistoryAppend (lowerNormalize p) one) true ∧
      lowerEndpoint (lowerHistoryAppend (lowerNormalize p) one) false <
        lowerEndpoint (lowerHistoryAppend (lowerNormalize p) two) true := by
    generalize lowerHistoryCommonOdd (lowerNormalize p) ⟨([],[]),(false,false)⟩ = c at k1 k2
    cases c
    · simp at k1 k2
      exact ⟨k1, k2⟩
    · simp at k1 k2
      exact ⟨k2, k1⟩
  have e1 : ∀ u, lowerEndpoint (lowerChild (lowerChild p l) ([1],[])) u =
      lowerEndpoint (lowerHistoryAppend (lowerNormalize p) one) u :=
    fun u => halign wide norm hmem hnorm 1 (by simp) u
  have e2 : ∀ u, lowerEndpoint (lowerChild (lowerChild p l) ([2],[])) u =
      lowerEndpoint (lowerHistoryAppend (lowerNormalize p) two) u :=
    fun u => halign wide norm hmem hnorm 2 (by simp) u
  refine ⟨max (lowerEndpoint (lowerChild (lowerChild p l) ([1],[])) false)
    (lowerEndpoint (lowerChild (lowerChild p l) ([2],[])) false), ?_, ?_⟩
  · refine Set.mem_Icc.2 ⟨le_max_left _ _, max_le (ho _) ?_⟩
    rw [e2, e1]
    exact le_of_lt hcross.1
  · refine Set.mem_Icc.2 ⟨le_max_right _ _, max_le ?_ (ho _)⟩
    rw [e1, e2]
    exact le_of_lt hcross.2
