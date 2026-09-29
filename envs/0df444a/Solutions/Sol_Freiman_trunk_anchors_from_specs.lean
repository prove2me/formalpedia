-- Prove2me | solution 1 for Freiman.trunk_anchors_from_specs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T12:42:38.661072+00:00
-- url     : https://prove2.me/submissions/fa0c4568-4f45-4e13-9bc4-801e8a3d5346

import Definitions.Def_Freiman_trunkGeometry
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_swap_nontie
import Mathlib.Tactic

open Freiman
namespace Anchors15

private theorem mode_parity (p : LowerPair) (k : Fin 16) (pi par : ℕ)
    (hm : TrunkMode p k pi par) : p.1.length % 2 = p.2.length % 2 := by
  have hC : (trunkCatalog.states k).context.parity = (false,false) := by
    fin_cases k <;> rfl
  have hf := hm.1.2.2
  rw [hC] at hf
  simp only [Bool.xor_false, Prod.fst, Prod.snd] at hf
  have hz : (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2 := by
    have he : ((lowerNormalize p).1.length % 2 = 1) ↔
        ((lowerNormalize p).2.length % 2 = 1) := by
      simpa only [decide_eq_decide] using hf
    omega
  unfold lowerNormalize at hz
  split_ifs at hz with hw
  · exact hz
  · exact hz.symm

private theorem normalized_endpoint (p : LowerPair)
    (hp : p.1.length % 2 = p.2.length % 2) (upper : Bool) :
    lowerEndpoint (lowerNormalize p) upper = lowerEndpoint p upper := by
  unfold lowerNormalize
  split_ifs with hw
  · rfl
  · have hne : lowerWidth p.1 ≠ lowerWidth p.2 := by
      intro h
      exact hw h.ge
    exact (lowerEarlyTerminal_endpoint_swap_nontie p ⟨hne,fun h => (h hp).elim⟩ upper).symm

private theorem empty_endpoint (p : LowerPair)
    (hp : p.1.length % 2 = p.2.length % 2) (upper : Bool) :
    trunkSpecLocalEndpoint p ([],[]) upper false = trunkParentEndpoint p upper := by
  simp only [trunkSpecLocalEndpoint, lowerHistoryOrient, Bool.false_eq_true,
    ↓reduceIte, lowerHistoryAppend, List.append_nil, Prod.eta, trunkParentEndpoint]
  rw [normalized_endpoint p hp, normalized_endpoint p hp]

private theorem upper_endpoint (p : LowerPair) (l : LowerLabel) :
    trunkSpecLocalEndpoint p (section14LabelWords l) true false = trunkLocalUpper p l := by
  simp [trunkSpecLocalEndpoint,lowerHistoryOrient,lowerHistoryAppend,section14LabelWords,
    trunkLocalUpper,lowerChild]

private theorem lower_endpoint (p : LowerPair) (l : LowerLabel) :
    trunkSpecLocalEndpoint p (section14LabelWords l) false false = lowerLocalLower p l := by
  simp [trunkSpecLocalEndpoint,lowerHistoryOrient,lowerHistoryAppend,section14LabelWords,
    lowerLocalLower,lowerChild]

private theorem anchors (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp) :
    (∀ l, (trunkPlanAt (trunkCatalog.states k) pi).labels.head? = some l →
      trunkParentEndpoint p true ≤ trunkLocalUpper p l) ∧
    (∀ l, (trunkPlanAt (trunkCatalog.states k) pi).labels.getLast? = some l →
      lowerLocalLower p l ≤ trunkParentEndpoint p false) := by
  have hp := mode_parity p k pi par hm
  constructor
  · intro l hl
    let sp : Section14Spec := ⟨section14LabelWords l,true,([],[]),true,false,[]⟩
    have hmem : sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi) := by
      unfold trunkSpecs
      apply List.mem_append_left
      apply List.mem_append_right
      simp [hl,sp]
    have hv := hs sp hmem (by simp [sp,trunkHolds])
    simpa only [sp,trunkSpecIncoming,List.head?_nil,Option.map_none,Option.getD_none,
      Bool.false_eq_true,↓reduceIte,empty_endpoint p hp,upper_endpoint] using hv
  · intro l hl
    let sp : Section14Spec := ⟨([],[]),false,section14LabelWords l,false,false,[]⟩
    have hmem : sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi) := by
      unfold trunkSpecs
      apply List.mem_append_right
      simp [hl,sp]
    have hv := hs sp hmem (by simp [sp,trunkHolds])
    simpa only [sp,trunkSpecIncoming,List.head?_nil,Option.map_none,Option.getD_none,
      Bool.false_eq_true,↓reduceIte,empty_endpoint p hp,lower_endpoint] using hv

end Anchors15

theorem solution (p : LowerPair) (k : Fin 16) (pi par : ℕ) (hm : TrunkMode p k pi par)
    (hs : ∀ sp ∈ trunkSpecs (trunkPlanAt (trunkCatalog.states k) pi), trunkSpecHolds p sp) :
    (∀ l, (trunkPlanAt (trunkCatalog.states k) pi).labels.head? = some l → trunkParentEndpoint p true ≤ trunkLocalUpper p l) ∧
    (∀ l, (trunkPlanAt (trunkCatalog.states k) pi).labels.getLast? = some l → lowerLocalLower p l ≤ trunkParentEndpoint p false) := by
  exact Anchors15.anchors p k pi par hm hs

#print axioms solution
