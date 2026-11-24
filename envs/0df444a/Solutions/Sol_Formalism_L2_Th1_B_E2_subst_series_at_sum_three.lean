-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.subst_series_at_sum_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:04:11.757681+00:00
-- url     : https://prove2.me/submissions/4a36ff30-a523-4918-8c04-8854338970ad

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E2
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.E2
theorem _root_.solution {ι : Type} (g : PowerSeries K) {b : Fin 3 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (evalSumThree g) = PowerSeries.subst (b 0 + b 1 + b 2) g := by
  unfold evalSumThree
  rw [psubst_subst g (u := (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 :
    MvPowerSeries (Fin 3) K)) (by simp) hb]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hb, map_add, map_add, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
end Formalism.L2.Th1.B.E2
