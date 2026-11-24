-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_otherWts_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:52:47.436796+00:00
-- url     : https://prove2.me/submissions/add0d494-055f-45e4-8a92-40ae537d7322

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_weightSp_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (lam : Fin n → ℤ) (z : MvPolynomial (Fin n × Fin n) ℚ)
    (hz : z ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) lam) (m : Fin n × Fin n →₀ ℕ) (hm : qn_wt m = lam) :
    coeff m z = 0 := by
  have hle : otherWts (glOps ℚ n (rowLetters n) Set.univ) lam ≤ LinearMap.ker (lcoeff ℚ m) := by
    unfold otherWts
    refine iSup₂_le fun mu hmu => ?_
    intro y hy
    rw [LinearMap.mem_ker, lcoeff_apply]
    exact qn_weightSp_coeff n mu y hy m (by rw [hm]; exact fun h => hmu h.symm)
  have := hle hz
  rwa [LinearMap.mem_ker, lcoeff_apply] at this
end Formalism.InvariantFactorPaths.ColumnFamilies
