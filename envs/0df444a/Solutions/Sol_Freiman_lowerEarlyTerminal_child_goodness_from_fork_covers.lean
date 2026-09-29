-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_child_goodness_from_fork_covers
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:16:46.268173+00:00
-- url     : https://prove2.me/submissions/14575266-580d-4947-9570-fc29020256dc

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic

open Freiman

theorem solution (p : LowerPair) (l : LowerLabel) (wide : Bool) (norm : CertBound)
    (hm : (wide,norm) ∈ section14NormalCases (section14LabelWords l))
    (ha : lowerEarlyTerminalAt p [norm])
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true)
    (hc : ∀ d ∈ ([1,2] : List ℕ+), lowerCover (lowerEarlyTerminalForkPair p l wide d) ⊆
      lowerCover (lowerChild (lowerChild p l) ([d],[]))) (h : ∀ req ∈ lowerEarlyTerminalGoodRequirements [] l,
      lowerEarlyTerminalAt p req.1 → lowerEarlyTerminalKindHolds p req.2) :
    lowerGood (lowerChild p l) := by
  set w := section14LabelWords l with hw
  set one := lowerHistorySet w wide (lowerHistoryPick w wide ++ [1]) with hone
  set two := lowerHistorySet w wide (lowerHistoryPick w wide ++ [2]) with htwo
  have hr1 : (([] ++ [norm] : List CertBound),
      LowerEarlyTerminalKind.compare one true two false true)
      ∈ lowerEarlyTerminalGoodRequirements [] l := by
    unfold lowerEarlyTerminalGoodRequirements
    refine List.mem_flatMap.mpr ⟨(wide,norm), hm, ?_⟩
    simp only [hone, htwo]
    simp [hw]
  have hr2 : (([] ++ [norm] : List CertBound),
      LowerEarlyTerminalKind.compare two true one false true)
      ∈ lowerEarlyTerminalGoodRequirements [] l := by
    unfold lowerEarlyTerminalGoodRequirements
    refine List.mem_flatMap.mpr ⟨(wide,norm), hm, ?_⟩
    simp only [hone, htwo]
    simp [hw]
  have h1 := h _ hr1 (by simpa using ha)
  have h2 := h _ hr2 (by simpa using ha)
  have hf1 : lowerHistoryAppend (lowerNormalize p) one
      = lowerEarlyTerminalForkPair p l wide 1 := rfl
  have hf2 : lowerHistoryAppend (lowerNormalize p) two
      = lowerEarlyTerminalForkPair p l wide 2 := rfl
  simp only [lowerEarlyTerminalKindHolds, lowerEarlyTerminalEndpoint, lowerHistoryEndpointReal,
    if_true, hf1, hf2] at h1 h2
  have key : lowerEndpoint (lowerEarlyTerminalForkPair p l wide 2) false
        ≤ lowerEndpoint (lowerEarlyTerminalForkPair p l wide 1) true ∧
      lowerEndpoint (lowerEarlyTerminalForkPair p l wide 1) false
        ≤ lowerEndpoint (lowerEarlyTerminalForkPair p l wide 2) true := by
    cases hoo : lowerHistoryCommonOdd (lowerNormalize p) ⟨([],[]),(false,false)⟩ with
    | false =>
      rw [hoo] at h1 h2
      norm_num at h1 h2
      exact ⟨by linarith, by linarith⟩
    | true =>
      rw [hoo] at h1 h2
      norm_num at h1 h2
      exact ⟨by linarith, by linarith⟩
  obtain ⟨hab, hba⟩ := key
  unfold lowerGood
  refine ⟨max (lowerEndpoint (lowerEarlyTerminalForkPair p l wide 1) false)
    (lowerEndpoint (lowerEarlyTerminalForkPair p l wide 2) false), ?_, ?_⟩
  · refine hc 1 (by simp) ?_
    unfold lowerCover
    exact Set.mem_Icc.mpr ⟨le_max_left _ _, max_le (ho _) hab⟩
  · refine hc 2 (by simp) ?_
    unfold lowerCover
    exact Set.mem_Icc.mpr ⟨le_max_right _ _, max_le hba (ho _)⟩
