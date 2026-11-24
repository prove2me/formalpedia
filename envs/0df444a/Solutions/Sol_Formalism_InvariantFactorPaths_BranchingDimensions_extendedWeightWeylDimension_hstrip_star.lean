-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.hstrip_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:39.829898+00:00
-- url     : https://prove2.me/submissions/14506fce-a4bf-4ba2-8987-bce8b9ce3871

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
theorem _root_.solution {n : ℕ} {a b : Fin n → ℤ} (h : HStrip n (extW a) (extW b)) :
    HStrip n (extW (star b)) (extW (star a)) := by
  constructor
  · intro m hm
    rw [extW_star _ hm, extW_star _ hm]
    have := h.1 (n - 1 - m) (by omega)
    omega
  · intro m hm
    rw [extW_star _ hm, extW_star _ (by omega : m < n)]
    have := h.2 (n - 1 - (m + 1)) (by omega)
    have e : n - 1 - (m + 1) + 1 = n - 1 - m := by omega
    rw [e] at this
    omega
end Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
