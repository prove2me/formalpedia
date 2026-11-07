-- Prove2me | solution 1 for EDPHardness.IntegralityGap.theorem_5_integrality_gap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T09:47:37.306437+00:00
-- url     : https://prove2.me/submissions/a833b312-810d-4c8b-b4a6-eed199cb54b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance
import Theorems.Thm_EDPHardness_IntegralityGap_good_event
import Theorems.Thm_EDPHardness_IntegralityGap_fractional_solution
import Theorems.Thm_EDPHardness_IntegralityGap_routed_pairs_bound

open EDPHardness.IntegralityGap

theorem solution :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ c : ℕ, 2 ≤ c →
      (c : ℝ) ≤ α * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) →
      ∃ H : Hyp n (numEdges n c) c,
        (∃ F : FracSol (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)),
          F.value = (n : ℝ) / c) ∧
        ∀ R : IntRouting (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)) (c - 1),
          (R.routed.card : ℝ) ≤ 4 * (n : ℝ) / beta1 n c := by
  classical
  obtain ⟨α₁, hα₁, N₁, h₁⟩ := good_event
  obtain ⟨α₂, hα₂, N₂, h₂⟩ := routed_pairs_bound
  refine ⟨min α₁ α₂, lt_min hα₁ hα₂, max N₁ N₂, ?_⟩
  intro n hn c hc hcα
  set r := Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) with hr
  have hcα' : (c : ℝ) ≤ min α₁ α₂ * r := by rw [hr, ← mul_div_assoc]; exact hcα
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hr0 : 0 < r := by
    by_contra h
    push_neg at h
    have : min α₁ α₂ * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (lt_min hα₁ hα₂)) h
    linarith
  have hc1 : (c : ℝ) ≤ α₁ * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) := by
    rw [mul_div_assoc, ← hr]
    exact hcα'.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hr0.le)
  have hc2 : (c : ℝ) ≤ α₂ * Real.logb 2 (Real.logb 2 n) / Real.logb 2 (Real.logb 2 (Real.logb 2 n)) := by
    rw [mul_div_assoc, ← hr]
    exact hcα'.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hr0.le)
  have hg := h₁ n (le_of_max_le_left hn) c hc hc1
  -- extract a good hypergraph
  have hex : ∃ H : Hyp n (numEdges n c) c,
      ¬ E1 n c H ∧ ¬ E2 n c H ∧ ¬ E3 n c (2 * gParam n c) H := by
    by_contra hne
    push_neg at hne
    unfold hypProb at hg
    have : (Finset.univ.filter
        (fun H : Hyp n (numEdges n c) c => ¬ E1 n c H ∧ ¬ E2 n c H ∧ ¬ E3 n c (2 * gParam n c) H))
        = ∅ := by
      ext H
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro ⟨a, b, d⟩
      exact d (hne H a b)
    rw [Finset.card_eq_zero.mpr (by convert this)] at hg
    simp at hg
    linarith
  obtain ⟨H, hE1, hE2, hE3⟩ := hex
  refine ⟨H, ?_, ?_⟩
  · obtain ⟨F, hF, -⟩ := fractional_solution n c hc H
    exact ⟨F, hF⟩
  · exact h₂ n (le_of_max_le_right hn) c hc hc2 H hE1 hE2 hE3
