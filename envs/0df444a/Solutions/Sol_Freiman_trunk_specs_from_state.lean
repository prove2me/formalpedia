-- Prove2me | solution 1 for Freiman.trunk_specs_from_state
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:58:15.682316+00:00
-- url     : https://prove2.me/submissions/c158332c-c4b6-4d95-9c43-3a059412cf02

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem solution (he : TrunkEndpointLaw) (hg : TrunkGreaterLaw)
    (ht : ∀ (p : LowerPair) (k : Fin 16), lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context →
      ∀ sp : Section14Spec, (∀ b ∈ trunkBranches (trunkCatalog.states k).context sp, trunkHolds b.1 (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) → lowerHistoryComparisonHolds b.2 (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p))) → trunkSpecHolds p sp)
    (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : trunkStateSound trunkCatalog k) :
    ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp := by
  intro sp hsp
  obtain ⟨hf, hrect, hpi, hpar, hbase⟩ := hm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hsp
  apply ht p k hf
  intro b hb hb1
  have hgb : trunkGoalBranches (trunkCatalog.states k) pi (i+1) =
      trunkBranches (trunkCatalog.states k).context (trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi))[i] := by
    unfold trunkGoalBranches
    rw [if_neg (by omega)]
    simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hi, Option.getD_some]
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  have key := hs pi par hpi hpar _ _ _ hrect hbase (i+1) (by omega) (by omega) j (by rw [hgb]; exact hj)
  have hbr : trunkBranch (trunkCatalog.states k) pi (i+1) j =
      (trunkBranches (trunkCatalog.states k).context (trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi))[i])[j] := by
    unfold trunkBranch
    rw [hgb]
    simp [List.getElem?_eq_getElem hj]
  rw [hbr] at key
  exact key hb1
