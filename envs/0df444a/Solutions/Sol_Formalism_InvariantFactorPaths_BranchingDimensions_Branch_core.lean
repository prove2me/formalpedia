-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Branch.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:43:35.355114+00:00
-- url     : https://prove2.me/submissions/25cd8348-77dd-416c-af75-00eb28bc8818

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_ff_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_sum_ff
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_det_vandermonde_eq_ff
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_sum_det
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_det_diff

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
open Formalism.InvariantFactorPaths.BranchingDimensions.Branch
namespace Formalism.InvariantFactorPaths.BranchingDimensions.Branch
theorem _root_.solution {n : ℕ} (mu : Fin (n + 1) → ℤ) (h : ∀ i : Fin n, mu i.succ ≤ mu i.castSucc) :
    (∏ j : Fin n, ((j : ℝ) + 1)) *
      ∑ la ∈ Fintype.piFinset (fun i : Fin n => Icc (mu i.succ) (mu i.castSucc)),
        (Matrix.vandermonde fun i : Fin n => (i : ℝ) - (la i : ℝ)).det =
      (Matrix.vandermonde fun i : Fin (n + 1) => (i : ℝ) - (mu i : ℝ)).det := by
  simp_rw [det_vandermonde_eq_ff]
  rw [sum_det (fun i : Fin n => Icc (mu i.succ) (mu i.castSucc)) (fun i x j => ff j ((i : ℝ) - (x : ℝ))),
    ← Matrix.det_mul_row, det_diff _ (by intro i; simp [ff_zero])]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [sum_ff _ _ _ _ (h i)]
  simp
end Formalism.InvariantFactorPaths.BranchingDimensions.Branch
