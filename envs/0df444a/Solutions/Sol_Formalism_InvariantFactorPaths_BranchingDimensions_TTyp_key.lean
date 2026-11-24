-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:10.973808+00:00
-- url     : https://prove2.me/submissions/ef51818f-80ff-4355-9ea6-ab36e8176169

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_lat_shift
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_bracket

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
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
theorem _root_.solution (h31 : LogBinomialProperties) (h34 : LogBinomialDeficit) (k' K : ℕ) (la : ℕ → ℤ) (q : ℕ → Bool) (B : ℕ → ℕ) (n0 : ℕ)
    (hk : 1 ≤ k')
    (h1 : ∀ l, l < (lat q B n0).length → k' ≤ (lat q B n0).getD l 0)
    (h2 : ∀ l, l + 1 < (lat q B n0).length → 4 * (lat q B n0).getD (l + 1) 0 ≤ (lat q B n0).getD l 0)
    (h3 : ∀ u, tailPos K la u ≤ (((lat q B n0).drop u).sum : ℕ))
    (i₀ u : ℕ) (X : ℝ) (hX : 0 < X)
    (hd : ((tailPos K la (u + ((Icc (i₀ + 1) n0).filter (fun l => q l = true)).card) : ℤ) : ℝ) ≤
      ((((lat q B n0).drop (u + ((Icc (i₀ + 1) n0).filter (fun l => q l = true)).card)).sum : ℕ) : ℝ)
        - X) :
    u < (lat q B (min i₀ n0)).length ∧
    (∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ)) -
      (∑ l ∈ range (lat q B n0).length, fT k' (((lat q B n0).getD l 0 : ℕ) : ℝ)) ≤
        -(X * k' / (4 * (((lat q B (min i₀ n0)).getD u 0 : ℕ) : ℝ))) := by
  have hcard : ((Icc (i₀ + 1) n0).filter (fun l => q l = true)).card =
      ((Icc (min i₀ n0 + 1) n0).filter (fun l => q l = true)).card := by
    by_cases h : i₀ ≤ n0
    · rw [min_eq_left h]
    · rw [min_eq_right (by omega), Finset.Icc_eq_empty_of_lt (by omega : n0 < i₀ + 1),
        Finset.Icc_eq_empty_of_lt (by omega : n0 < n0 + 1)]
  obtain ⟨hsh1, hsh2⟩ := lat_shift q B (min_le_right i₀ n0)
  rw [hcard] at hd
  obtain ⟨hlt, hbd⟩ := (bracket h31 h34 k' K la (lat q B n0) hk h1 h2 h3).2 _ X hX hd
  rw [hsh1 u] at hbd
  exact ⟨by omega, hbd⟩
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
