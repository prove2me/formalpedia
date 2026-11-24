-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.dom_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:40.084523+00:00
-- url     : https://prove2.me/submissions/2bb55726-3988-4c26-8058-befcc78bff22

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
theorem _root_.solution {n : ℕ} {a : Fin n → ℤ} (h : Dom n (extW a)) : Dom n (extW (star a)) := by
  intro m hm
  rw [extW_star _ hm, extW_star _ (by omega : m < n)]
  have := h (n - 1 - (m + 1)) (by omega)
  have e : n - 1 - (m + 1) + 1 = n - 1 - m := by omega
  rw [e] at this
  omega
end Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
