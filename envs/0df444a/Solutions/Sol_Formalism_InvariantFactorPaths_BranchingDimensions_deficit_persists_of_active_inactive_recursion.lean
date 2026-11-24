-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.deficit_persists_of_active_inactive_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:59.131798+00:00
-- url     : https://prove2.me/submissions/871c2c20-97df-4342-b960-6cb4e3e52965

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_card_filter_Icc_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (N : ℕ) (T : ℕ → ℕ → ℤ) (S : ℕ → ℕ → ℕ) (act : ℕ → Bool)
    (hA : ∀ i u, i < N → act (i + 1) = true → T (i + 1) (u + 1) ≤ T i u ∧ S (u + 1) (i + 1) = S u i)
    (hI : ∀ i u, i < N → act (i + 1) = false → T (i + 1) u ≤ T i u ∧ S u (i + 1) = S u i)
    (i₀ u : ℕ) (X : ℝ) (h : ((T i₀ u : ℤ) : ℝ) ≤ (S u i₀ : ℝ) - X) :
    ∀ i, i₀ ≤ i → i ≤ N →
      ((T i (u + ((Icc (i₀ + 1) i).filter fun l => act l = true).card) : ℤ) : ℝ) ≤
        (S (u + ((Icc (i₀ + 1) i).filter fun l => act l = true).card) i : ℝ) - X := by
  intro i hi hiN
  induction i, hi using Nat.le_induction with
  | base =>
    have hc : ((Icc (i₀ + 1) i₀).filter fun l => act l = true).card = 0 := by simp
    rw [hc, add_zero]
    exact h
  | succ i hi ih =>
    have ih' := ih (by omega)
    rw [card_filter_Icc_succ _ (i₀ + 1) i (by omega)]
    generalize hc : ((Icc (i₀ + 1) i).filter fun l => act l = true).card = c at ih' ⊢
    split_ifs with ha
    · obtain ⟨h1, h2⟩ := hA i (u + c) (by omega) ha
      rw [← add_assoc, h2]
      have h1' : ((T (i + 1) (u + c + 1) : ℤ) : ℝ) ≤ ((T i (u + c) : ℤ) : ℝ) := by exact_mod_cast h1
      linarith
    · rw [add_zero]
      have ha' : act (i + 1) = false := by simpa using ha
      obtain ⟨h1, h2⟩ := hI i (u + c) (by omega) ha'
      rw [h2]
      have h1' : ((T (i + 1) (u + c) : ℤ) : ℝ) ≤ ((T i (u + c) : ℤ) : ℝ) := by exact_mod_cast h1
      linarith
end Formalism.InvariantFactorPaths.BranchingDimensions
