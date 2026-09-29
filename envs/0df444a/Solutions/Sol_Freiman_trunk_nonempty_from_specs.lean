-- Prove2me | solution 1 for Freiman.trunk_nonempty_from_specs
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:55:26.206221+00:00
-- url     : https://prove2.me/submissions/fff075f6-4b76-408c-b3f4-69bdf984afb4

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

/-- a weak specification with no extra premises, read in both parities -/
lemma spec_le (p : LowerPair) (a b : LowerPair) (ua ub : Bool)
    (h : trunkSpecHolds p ⟨a, ua, b, ub, false, []⟩) :
    ((lowerNormalize p).1.length % 2 = 0 →
      lowerEndpoint (lowerHistoryAppend (lowerNormalize p) b) ub ≤
        lowerEndpoint (lowerHistoryAppend (lowerNormalize p) a) ua) ∧
    (¬ (lowerNormalize p).1.length % 2 = 0 →
      lowerEndpoint (lowerHistoryAppend (lowerNormalize p) a) (!ua) ≤
        lowerEndpoint (lowerHistoryAppend (lowerNormalize p) b) (!ub)) := by
  have h' := h (by intro x hx; simp at hx)
  constructor
  · intro hc
    simp [trunkSpecLocalEndpoint, trunkSpecIncoming, lowerHistoryOrient, hc] at h'
    linarith
  · intro hc
    simp [trunkSpecLocalEndpoint, trunkSpecIncoming, lowerHistoryOrient, hc] at h'
    linarith

lemma append_eq_child (p : LowerPair) (l : LowerLabel) :
    lowerHistoryAppend (lowerNormalize p) (section14LabelWords l) = lowerChild p l := rfl

lemma inside_mem (plan : TrunkPlan) (l : LowerLabel) (hl : l ∈ plan.labels) :
    (⟨section14LabelWords l, true, section14LabelWords l, false, false, []⟩ : Section14Spec) ∈
      trunkSpecs plan := by
  unfold trunkSpecs
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (List.mem_flatMap.2 ⟨l, hl, List.mem_cons_self ..⟩)))

/-- own-interval order of a listed child -/
lemma own_order (p : LowerPair) (plan : TrunkPlan) (hs : ∀ sp ∈ trunkSpecs plan, trunkSpecHolds p sp)
    (l : LowerLabel) (hl : l ∈ plan.labels) :
    lowerEndpoint (lowerChild p l) false ≤ lowerEndpoint (lowerChild p l) true := by
  have h := spec_le p _ _ _ _ (hs _ (inside_mem plan l hl))
  rw [append_eq_child] at h
  by_cases hc : (lowerNormalize p).1.length % 2 = 0
  · exact h.1 hc
  · simpa using h.2 hc

theorem solution (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp) :
    ∀ l ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels, (lowerCover (lowerChild p l)).Nonempty := by
  intro l hl
  exact ⟨lowerEndpoint (lowerChild p l) false, Set.mem_Icc.2 ⟨le_rfl, own_order p _ hs l hl⟩⟩
