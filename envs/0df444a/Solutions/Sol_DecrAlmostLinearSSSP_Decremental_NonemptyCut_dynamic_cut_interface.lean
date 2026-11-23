-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.NonemptyCut.dynamic_cut_interface
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:09.610627+00:00
-- url     : https://prove2.me/submissions/2bfa9515-57f6-4869-b0c0-8f5b1540cc52
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_dynamic_tree_cut_sparsifier
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_tree_cut_public_wrapper

set_option autoImplicit false
open scoped ENNReal NNReal

open DecrAlmostLinearSSSP.Decremental DecrAlmostLinearSSSP.Decremental.NonemptyCut

/-- The external normalized tree structure and the charged scaling/report wrapper
combine to the implemented dynamic-cut interface. -/
theorem solution :
    ∀ exponent : ℕ, ∃ (impl : Implementation) (K h Γ a : ℕ → ℝ) (C : ℝ),
      0 < C ∧ Subpolynomial K ∧ Subpolynomial h ∧ Subpolynomial Γ ∧ Subpolynomial a ∧
      (∀ m, 32 ≤ K m ∧ K m ≤ Real.rpow 2
        (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
          max 1 (Real.log (Real.log (max 2 m : ℕ))))) ∧
      ∀ m ξ, 0 < ξ → Implements impl m exponent (K m) (h m) (Γ m)
        (C * m * a m) ξ := by
  intro exponent
  obtain ⟨tree, K₀, h₀, a₀, C₀, hC₀, hK₀, hh₀, ha₀, hquality, htree⟩ :=
    dynamic_tree_cut_sparsifier exponent
  exact tree_cut_public_wrapper exponent tree K₀ h₀ a₀ C₀ hC₀ hK₀ hh₀ ha₀ hquality htree