-- Prove2me | solution 1 for Formalism.L2.Th1.H.exp_series_entire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:39.412122+00:00
-- url     : https://prove2.me/submissions/96cd6cd8-d269-4e0e-a242-6321ea95d581

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
import Theorems.Thm_Formalism_L2_Th1_H_expFPS_radius
import Theorems.Thm_Formalism_L2_Th1_H_expFPS_hasSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : ExpSeriesEntire := by
  unfold ExpSeriesEntire
  intro V _ _ X c ℓ h z _
  have hfps : HasFPowerSeriesOnBall (fun z => ∑' x, c x * Complex.exp (ℓ x z)) (expFPS c ℓ) 0 ⊤ :=
    { r_le := by rw [expFPS_radius c ℓ h]
      r_pos := ENNReal.zero_lt_top
      hasSum := fun {y} _ => by simpa using expFPS_hasSum c ℓ h y }
  exact hfps.analyticAt_of_mem (by simp)
end Formalism.L2.Th1.H
