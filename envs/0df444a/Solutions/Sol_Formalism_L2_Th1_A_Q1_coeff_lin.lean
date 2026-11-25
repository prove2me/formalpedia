-- Prove2me | solution 1 for Formalism.L2.Th1.A.Q1.coeff_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:58:24.872709+00:00
-- url     : https://prove2.me/submissions/21d779bc-defb-4c87-9d9a-ede118a69f40

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DifferenceLinearCoeff
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
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
theorem _root_.solution (n : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.coeff (Finsupp.single 0 1) ((U₁ - U₂) * n) = cc n := by
  classical
  have h10 : ¬ (Finsupp.single (1 : Fin 2) 1 ≤ Finsupp.single (0 : Fin 2) 1) := by
    intro h
    have := h 1
    simp at this
  show MvPowerSeries.coeff (Finsupp.single 0 1) ((MvPowerSeries.X 0 - MvPowerSeries.X 1) * n) = cc n
  rw [sub_mul, map_sub, MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul,
    MvPowerSeries.coeff_monomial_mul, if_pos le_rfl, if_neg h10, tsub_self, one_mul, sub_zero,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
end Formalism.L2.Th1.A.Q1
