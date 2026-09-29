-- Prove2me | solution 1 for Freiman.lowerHistory_catalog_shapes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T09:37:16.336848+00:00
-- url     : https://prove2.me/submissions/7b0193be-632f-4a9a-9d14-f233e7ed5a58

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def legalDecidable (s : LowerHistoryState) :
    (steps : List (LowerLabel × Bool)) → Decidable (lowerHistoryLegalSteps s steps)
  | [] => Decidable.isTrue trivial
  | (l,r) :: tail =>
      match (inferInstance : Decidable (lowerHistoryStepLegal s l r)) with
      | Decidable.isTrue hs =>
          match legalDecidable (lowerHistoryAdvance s l r) tail with
          | Decidable.isTrue ht => Decidable.isTrue ⟨hs, ht⟩
          | Decidable.isFalse ht => Decidable.isFalse (fun h => ht h.2)
      | Decidable.isFalse hs => Decidable.isFalse (fun h => hs h.1)

private def structuralDecidable (p : LowerHistoryPath) :
    Decidable (lowerHistoryStructural p) := by
  letI : Decidable (lowerHistoryLegalSteps
      (lowerHistoryInitialState p) p.steps) :=
    legalDecidable (lowerHistoryInitialState p) p.steps
  unfold lowerHistoryStructural
  infer_instance

private def shardDecidable (xs : Array LowerHistoryPath) :
    Decidable (∀ p ∈ xs.toList, lowerHistoryStructural p) :=
  @List.decidableBAll _ (fun p => lowerHistoryStructural p)
    (fun p => structuralDecidable p) xs.toList

private theorem hL : ∀ p ∈ lowerHistoryPathsL.toList, lowerHistoryStructural p := by
  let d := shardDecidable lowerHistoryPathsL
  have hd : @decide _ d = true := by decide +kernel
  exact @of_decide_eq_true _ d hd

private theorem hR : ∀ p ∈ lowerHistoryPathsR.toList, lowerHistoryStructural p := by
  let d := shardDecidable lowerHistoryPathsR
  have hd : @decide _ d = true := by decide +kernel
  exact @of_decide_eq_true _ d hd

private theorem hM : ∀ p ∈ lowerHistoryPathsM.toList, lowerHistoryStructural p := by
  let d := shardDecidable lowerHistoryPathsM
  have hd : @decide _ d = true := by decide +kernel
  exact @of_decide_eq_true _ d hd

private theorem hX : ∀ p ∈ lowerHistoryPathsX.toList, lowerHistoryStructural p := by
  let d := shardDecidable lowerHistoryPathsX
  have hd : @decide _ d = true := by decide +kernel
  exact @of_decide_eq_true _ d hd

private theorem hH : ∀ p ∈ lowerHistoryPathsH.toList, lowerHistoryStructural p := by
  let d := shardDecidable lowerHistoryPathsH
  have hd : @decide _ d = true := by decide +kernel
  exact @of_decide_eq_true _ d hd

theorem solution : ∀ p ∈ lowerHistoryPaths.toList, lowerHistoryStructural p := by
  intro p hp
  have hp' :
      p ∈ lowerHistoryPathsL.toList ∨ p ∈ lowerHistoryPathsR.toList ∨
      p ∈ lowerHistoryPathsM.toList ∨ p ∈ lowerHistoryPathsX.toList ∨
      p ∈ lowerHistoryPathsH.toList := by
    simpa [lowerHistoryPaths] using hp
  rcases hp' with hpL | hpR | hpM | hpX | hpH
  · exact hL p hpL
  · exact hR p hpR
  · exact hM p hpM
  · exact hX p hpX
  · exact hH p hpH
