-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.weylDim_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:40.121533+00:00
-- url     : https://prove2.me/submissions/daf52cc0-8e05-48b3-bca3-b297c91c2574

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_extW_star

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
open Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
namespace Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
theorem _root_.solution {n : ℕ} (a : Fin n → ℤ) : weylDim n (extW (star a)) = weylDim n (extW a) := by
  unfold weylDim
  rw [Finset.prod_sigma', Finset.prod_sigma']
  refine Finset.prod_nbij' (fun s => ⟨n - 1 - s.2, n - 1 - s.1⟩) (fun s => ⟨n - 1 - s.2, n - 1 - s.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ hs
    simp only [Finset.mem_sigma, mem_range] at hs ⊢
    omega
  · rintro ⟨j, i⟩ hs
    simp only [Finset.mem_sigma, mem_range] at hs ⊢
    omega
  · rintro ⟨j, i⟩ hs
    simp only [Finset.mem_sigma, mem_range] at hs
    have h1 : n - 1 - (n - 1 - j) = j := by omega
    have h2 : n - 1 - (n - 1 - i) = i := by omega
    simp only [h1, h2]
  · rintro ⟨j, i⟩ hs
    simp only [Finset.mem_sigma, mem_range] at hs
    have h1 : n - 1 - (n - 1 - j) = j := by omega
    have h2 : n - 1 - (n - 1 - i) = i := by omega
    simp only [h1, h2]
  · rintro ⟨j, i⟩ hs
    simp only [Finset.mem_sigma, mem_range] at hs
    have h1 : (((n - 1 - i : ℕ) : ℝ)) + i + 1 = n := by
      have : (n - 1 - i) + i + 1 = n := by omega
      exact_mod_cast this
    have h2 : (((n - 1 - j : ℕ) : ℝ)) + j + 1 = n := by
      have : (n - 1 - j) + j + 1 = n := by omega
      exact_mod_cast this
    have hd : (((n - 1 - i : ℕ) : ℝ)) - ((n - 1 - j : ℕ) : ℝ) = (j : ℝ) - i := by linarith
    simp only
    rw [hd, extW_star _ (by omega : i < n), extW_star _ hs.1]
    congr 2
    push_cast
    ring
end Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
