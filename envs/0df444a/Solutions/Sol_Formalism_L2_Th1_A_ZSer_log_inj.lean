-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.log_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:08:31.097857+00:00
-- url     : https://prove2.me/submissions/8e61097a-25b0-4ec7-ac13-eca0c6c72aa7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_log_cc
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_L2_Th1_A_composition_inverse_spec
import Theorems.Thm_Formalism_L2_Th1_A_expSpec_of
import Theorems.Thm_Formalism_L2_Th1_A_integration_spec
import Theorems.Thm_Formalism_L2_Th1_A_invariant_differential_units
import Theorems.Thm_Formalism_L2_Th1_A_subst_injective_of_leftInverse


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.ZSer
local notation "FF[" W "](" a ", " b ")" =>
  MvPowerSeries.subst (![a, b] : Fin 2 → PowerSeries _) (fgl W)
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
namespace Formalism.L2.Th1.A.ZSer
theorem _root_.solution {a b : K⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (h : (logSer W).subst a = (logSer W).subst b) : a = b := by
  have hel : (expSer W).subst (logSer W) = X :=
    ((expSpec_of integration_spec composition_inverse_spec invariant_differential_units) K W).2.2.2.1
  exact subst_injective_of_leftInverse (HasSubst.of_constantCoeff_zero' (log_cc W))
    (HasSubst.of_constantCoeff_zero' ha) (HasSubst.of_constantCoeff_zero' hb) hel h
end Formalism.L2.Th1.A.ZSer
