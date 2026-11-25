-- Prove2me | solution 1 for Formalism.L2.Th1.A.Two.tS_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:27:17.005533+00:00
-- url     : https://prove2.me/submissions/16896a05-be90-4bd1-af7d-d952c9fef02f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_iSerSpec
import Theorems.Thm_Formalism_L2_Th1_A_logNeg
import Theorems.Thm_Formalism_L2_Th1_A_tSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
namespace Formalism.L2.Th1.A.Two
theorem _root_.solution (xP : K) :
    PowerSeries.subst (-X : K⟦X⟧) ((tS W xP).subst (expSer W) : K⟦X⟧)
      = (tS W xP).subst (expSer W) := by
  have hX : HasSubst (-X : K⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  have hi : HasSubst (iSer W) := HasSubst.of_constantCoeff_zero' (iSerSpec K W).1
  have k1 := subst_comp_subst_apply (he W) hX (tS W xP)
  have k2 := subst_comp_subst_apply hi (he W) (tS W xP)
  rw [(tSpec K W xP).2.2.2.2.2] at k2
  rw [k1, (logNeg K W).2, ← k2]
end Formalism.L2.Th1.A.Two
