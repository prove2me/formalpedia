-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.subst_series_at_difference_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:04:51.291807+00:00
-- url     : https://prove2.me/submissions/24499876-fce6-4c98-af20-8f184d5ebd27

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
theorem _root_.solution {ι : Type} (j k : Fin 3) (g : PowerSeries K) {b : Fin 3 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (evalDiffThree j k g) = PowerSeries.subst (b j - b k) g := by
  unfold evalDiffThree
  rw [psubst_subst g (u := (MvPowerSeries.X j - MvPowerSeries.X k : MvPowerSeries (Fin 3) K))
    (by simp) hb]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
end Formalism.L2.Th1.B.E2
