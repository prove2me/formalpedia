-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl2.formal_logarithm_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:46:27.817585+00:00
-- url     : https://prove2.me/submissions/8ab15336-99e0-4cdd-85ff-d105ec88766e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowThird
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalLogarithmBaseChange
import Theorems.Thm_Formalism_L2_Th1_A_composition_inverse_spec
import Theorems.Thm_Formalism_L2_Th1_A_integration_spec
import Theorems.Thm_Formalism_L2_Th1_A_invariant_differential_units
import Theorems.Thm_Formalism_L2_Th1_A_logNeg_of


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
open Formalism.L2.Th1.A.Fgl2
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
namespace Formalism.L2.Th1.A.Fgl2
theorem _root_.solution : LogNeg.{u} := logNeg_of integration_spec composition_inverse_spec invariant_differential_units formal_inverse_spec
end Formalism.L2.Th1.A.Fgl2
