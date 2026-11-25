-- Prove2me | solution 1 for Formalism.L2.Th1.A.Q1.cc_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:06:20.724888+00:00
-- url     : https://prove2.me/submissions/9279c9f1-01d5-4c5e-9951-5ad4473bea63

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
theorem _root_.solution {σ τ : Type*} {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
    (ha' : ∀ i, cc (a i) = 0) (f : MvPowerSeries σ R) : cc (f.subst a) = cc f := by
  have h0 : cc (f - MvPowerSeries.C (cc f)) = 0 := by simp
  have h1 := MvPowerSeries.constantCoeff_subst_eq_zero ha ha' h0
  rw [MvPowerSeries.subst_sub ha, MvPowerSeries.subst_C, map_sub, MvPowerSeries.constantCoeff_C,
    sub_eq_zero] at h1
  exact h1
end Formalism.L2.Th1.A.Q1
