-- Prove2me | solution 1 for Formalism.L2.Th1.A.Q1.subst_XX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:02:09.242217+00:00
-- url     : https://prove2.me/submissions/0d909bfe-2d84-4fd9-be8b-62f9c1e13d46

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DifferenceLinearCoeff
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
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
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Q1
open CubeR
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A.Q1
theorem _root_.solution (G : MvPowerSeries (Fin 2) R) :
    G.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] = G := by
  have h : (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1])
      = (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) R) := by
    funext i
    fin_cases i <;> rfl
  simp only [h, MvPowerSeries.subst_self, id_eq]
end Formalism.L2.Th1.A.Q1
