-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.interl_of_path
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:42.117528+00:00
-- url     : https://prove2.me/submissions/f4c24ba6-0106-4f31-a70b-cedf121f40a0

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Ns_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stage_add

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
variable {D : Letters} {mu : D.Stages}
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (hW : D.Wf) (hP : D.IsPATH mu) (j : ℕ) (hj : j < D.r) :
    Interl (D.k - (j + 1)) (stage mu (D.n0 + (j + 1))) (stage mu (D.n0 + j)) := by
  intro l hl
  have hNs := Ns_eq hW
  have hv : D.vec (D.n0 + (j + 1)) = true := hW.2.2.2.2 _ (by omega) (by omega)
  have hS := hP.2.2.1 (D.n0 + (j + 1)) (by omega) (by omega) hv
  have e1 : D.n0 + (j + 1) - 1 = D.n0 + j := by omega
  rw [e1] at hS
  simp only [stage_add]
  constructor
  · rw [show l + (j + 1) = l + j + 1 by omega]
    exact hS.2 (l + j) (by omega)
  · rw [show l + 1 + j = l + (j + 1) by omega]
    exact hS.1 (l + (j + 1)) (by omega)
end Formalism.InvariantFactorPaths.BranchingDimensions
