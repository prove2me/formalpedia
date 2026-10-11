-- Prove2me | solution 1 for CompOT.Auction.eq_3_8
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:39:46.242229+00:00
-- url     : https://prove2.me/submissions/2fd30b99-eb3f-474a-8515-8337e08e801f

import Mathlib
import Definitions.Def_CompOT_Auction_Defs

open CompOT.Auction

theorem solution {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (h : ∀ i, C i (σ i) - g (σ i) = ⨅ j, (C i j - g j)) :
    (∀ τ : Equiv.Perm (Fin n), assignmentCost C σ ≤ assignmentCost C τ) ∧
      DualFeasible C (cbarTransform C g) g ∧
      ∀ f' g' : Fin n → ℝ, DualFeasible C f' g' →
        ∑ i, f' i + ∑ j, g' j ≤ ∑ i, cbarTransform C g i + ∑ j, g j := by
  classical
  have hlow (i j : Fin n) : cbarTransform C g i ≤ C i j - g j :=
    ciInf_le (Set.finite_range _).bddBelow j
  have hcost : assignmentCost C σ = ∑ i, cbarTransform C g i + ∑ j, g j := by
    have heq (i : Fin n) : C i (σ i) = cbarTransform C g i + g (σ i) := by
      have hi := h i
      change C i (σ i) - g (σ i) = cbarTransform C g i at hi
      linarith
    simp_rw [assignmentCost, heq]
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ g]
  refine ⟨?_, ?_, ?_⟩
  · intro τ
    have hb : ∑ i, (cbarTransform C g i + g (τ i)) ≤ ∑ i, C i (τ i) := by
      apply Finset.sum_le_sum
      intro i _
      linarith [hlow i (τ i)]
    rw [Finset.sum_add_distrib, Equiv.sum_comp τ g] at hb
    rw [hcost]
    exact hb
  · intro i j
    linarith [hlow i j]
  · intro f' g' hfg
    have hb : ∑ i, (f' i + g' (σ i)) ≤ ∑ i, C i (σ i) :=
      Finset.sum_le_sum (fun i _ => hfg i (σ i))
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ g'] at hb
    rw [← hcost]
    exact hb
