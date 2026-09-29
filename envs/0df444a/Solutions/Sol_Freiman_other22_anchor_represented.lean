-- Prove2me | solution 1 for Freiman.other22_anchor_represented
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-15T20:39:44.211566+00:00
-- url     : https://prove2.me/submissions/522f2e3b-eb63-4aa1-806f-8c0eef5f64f0

import Definitions.Def_Freiman_other22Verification
import Theorems.Thm_Freiman_lowerHistory_endpoint_semantics
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Mathlib.Tactic

open Freiman
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

-- Endpoint nonnegativity lemmas reused from accepted submission
-- d769562b-25b8-4db6-b0a7-965e4e05818d.
namespace M7Goodness14

private theorem prefix_nonneg (w : List ℕ+) (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ prefixEval w z := by
  induction w with
  | nil => exact hz
  | cons a w ih =>
    simp only [prefixEval]
    positivity

private theorem tau_nonneg : 0 ≤ certFieldVal lowerHistoryTau := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  norm_num [certFieldVal, lowerHistoryTau]

private theorem endval_nonneg (C : LowerHistoryContext) (w : LowerPair)
    (upper side short : Bool) :
    0 ≤ certFieldVal (lowerHistoryEndVal C w upper side short) := by
  unfold lowerHistoryEndVal
  rw [lowerHistory_cf_value _ _ tau_nonneg]
  exact prefix_nonneg _ _ tau_nonneg

private theorem equal_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool)
    (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEqualCases C w upper) :
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2 := by
  by_cases hn : (lowerHistoryNatural C w upper false ||
      lowerHistoryNatural C w upper true) = true
  · simp only [lowerHistoryEqualCases, hn, ↓reduceIte,
      List.mem_singleton, Prod.mk.injEq] at hz
    rcases hz with ⟨rfl, rfl⟩
    exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩
  · dsimp only [lowerHistoryEqualCases] at hz
    rw [if_neg hn] at hz
    simp only [List.mem_flatMap, List.mem_map] at hz
    obtain ⟨⟨wide,norm⟩, _, shortened, _, heq⟩ := hz
    cases heq
    exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩

private theorem endpoint_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool)
    (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEndpointCases C w upper) :
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2 := by
  unfold lowerHistoryEndpointCases at hz
  split_ifs at hz with hp
  · exact equal_nonneg C w upper z cs hz
  · simp only [List.mem_flatMap, List.mem_map] at hz
    obtain ⟨⟨wide,norm⟩, _, ⟨v,bs⟩, hv, heq⟩ := hz
    cases heq
    split_ifs at hv
    · exact equal_nonneg _ _ _ _ _ hv
    · simp only [List.mem_singleton, Prod.mk.injEq] at hv
      rcases hv with ⟨rfl, rfl⟩
      exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩


end M7Goodness14

private theorem anchor_value (Z : LowerPair) (hn : lowerNormalize Z = Z)
    (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    other22AnchorValue Z = lowerHistoryEndpointReal Z (other22Context k)
      (other22Ancestor k) (other22AncestorUpper k) := by
  have hs : lowerEnds Z.1 [3,1] ↔ lowerEnds (other22Paths k).context [3,1] := hc.1.2.2
  rcases Nat.mod_two_eq_zero_or_one Z.1.length with he | he
  · have ho : ¬ Z.1.length % 2 = 1 := by omega
    by_cases hx : lowerEnds Z.1 [3,1]
    · have hy := hs.mp hx
      simp only [lowerEnds] at hy
      simp [other22AnchorValue, hx, other22Ancestor, other22AncestorUpper,
        lowerBaseLower, lowerHistoryEndpointReal, lowerHistoryCommonOdd,
        other22Context, lowerHistoryAppend, hn, he, ho, hy]
    · have hy : ¬ lowerEnds (other22Paths k).context [3,1] := fun hz => hx (hs.mpr hz)
      simp only [lowerEnds] at hy
      simp [other22AnchorValue, hx, other22Ancestor, other22AncestorUpper,
        lowerChildUpper, lowerChild, lowerHistoryEndpointReal, lowerHistoryCommonOdd,
        other22Context, lowerHistoryAppend, hn, he, ho, hy]
  · have ho : ¬ Z.1.length % 2 = 0 := by omega
    by_cases hx : lowerEnds Z.1 [3,1]
    · have hy := hs.mp hx
      simp only [lowerEnds] at hy
      simp [other22AnchorValue, hx, other22Ancestor, other22AncestorUpper,
        lowerBaseLower, lowerHistoryEndpointReal, lowerHistoryCommonOdd,
        other22Context, lowerHistoryAppend, hn, he, ho, hy]
    · have hy : ¬ lowerEnds (other22Paths k).context [3,1] := fun hz => hx (hs.mpr hz)
      simp only [lowerEnds] at hy
      simp [other22AnchorValue, hx, other22Ancestor, other22AncestorUpper,
        lowerChildUpper, lowerChild, lowerHistoryEndpointReal, lowerHistoryCommonOdd,
        other22Context, lowerHistoryAppend, hn, he, ho, hy]

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    other22EndpointRepresented Z (other22Context k) (other22Ancestor k)
      (other22AncestorUpper k) (other22AnchorValue Z) := by
  obtain ⟨z,cs,hcase,hholds,hvalue⟩ := lowerHistory_endpoint_semantics Z
    (other22Context k) hc (other22Ancestor k) (other22AncestorUpper k)
  have hnonneg := M7Goodness14.endpoint_nonneg (other22Context k)
    (other22Ancestor k) (other22AncestorUpper k) z cs hcase
  exact ⟨z,cs,hcase,hholds,(anchor_value Z h.normalizedZ k hc).trans hvalue,
    hnonneg.1,hnonneg.2⟩
