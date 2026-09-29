-- Prove2me | solution 1 for Freiman.trunk_contacts_from_specs
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:52:48.991614+00:00
-- url     : https://prove2.me/submissions/0c4a901f-af9f-4206-b09b-0a11e5b6a97d

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
    ∀ lm ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels.zip (trunkPlanAt (trunkCatalog.states k) pi).labels.tail, lm ∉ (trunkPlanAt (trunkCatalog.states k) pi).holes →
    (lowerCover (lowerChild p lm.1) ∩ lowerCover (lowerChild p lm.2)).Nonempty := by
  intro lm hlm hnot
  obtain ⟨l, m⟩ := lm
  have hl : l ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels := (List.of_mem_zip hlm).1
  have hm' : m ∈ (trunkPlanAt (trunkCatalog.states k) pi).labels :=
    List.mem_of_mem_tail (List.of_mem_zip hlm).2
  have hol := own_order p _ hs l hl
  have hom := own_order p _ hs m hm'
  -- the two contact specifications
  have hmem : ∀ x ∈ ([⟨section14LabelWords l, true, section14LabelWords m, false, false, []⟩,
      ⟨section14LabelWords m, true, section14LabelWords l, false, false, []⟩] : List Section14Spec),
      x ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi) := by
    intro x hx
    unfold trunkSpecs
    simp only [List.mem_append]
    refine Or.inl (Or.inl (Or.inr (List.mem_flatMap.2 ⟨(l, m), hlm, ?_⟩)))
    simp only [hnot, ↓reduceIte]
    exact hx
  have h1 := spec_le p _ _ _ _ (hs _ (hmem ⟨section14LabelWords l, true, section14LabelWords m, false, false, []⟩ (by simp)))
  have h2 := spec_le p _ _ _ _ (hs _ (hmem ⟨section14LabelWords m, true, section14LabelWords l, false, false, []⟩ (by simp)))
  rw [append_eq_child, append_eq_child] at h1 h2
  have hcross : lowerEndpoint (lowerChild p m) false ≤ lowerEndpoint (lowerChild p l) true ∧
      lowerEndpoint (lowerChild p l) false ≤ lowerEndpoint (lowerChild p m) true := by
    by_cases hc : (lowerNormalize p).1.length % 2 = 0
    · exact ⟨h1.1 hc, h2.1 hc⟩
    · exact ⟨by simpa using h2.2 hc, by simpa using h1.2 hc⟩
  show (lowerCover (lowerChild p l) ∩ lowerCover (lowerChild p m)).Nonempty
  refine ⟨max (lowerEndpoint (lowerChild p l) false) (lowerEndpoint (lowerChild p m) false), ?_, ?_⟩
  · exact Set.mem_Icc.2 ⟨le_max_left _ _, max_le hol hcross.1⟩
  · exact Set.mem_Icc.2 ⟨le_max_right _ _, max_le hcross.2 hom⟩
