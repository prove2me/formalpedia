-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.law_with_inverse_factor_difference
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:26:04.335333+00:00
-- url     : https://prove2.me/submissions/9bd20b0d-1fce-401f-b22b-5228a921898c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_L2_Th1_B_E2_cX
import Theorems.Thm_Formalism_L2_Th1_B_E2_law_with_inverse_three_eq_subst
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
variable {K : Type} [NormedField K] [CharZero K]
namespace Formalism.L2.Th1.B.E2
theorem _root_.solution {F n : MvPowerSeries (Fin 2) K} {i : PowerSeries K}
    (hi : PowerSeries.constantCoeff i = 0)
    (hn : FI F i = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * n) (j k : Fin 3) :
    lawDifferenceThree F i j k = (MvPowerSeries.X j - MvPowerSeries.X k) * MvPowerSeries.subst
      ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] n := by
  have hb := hs2 (cX (K := K) j) (cX (K := K) k)
  rw [law_with_inverse_three_eq_subst hi j k, hn, ← MvPowerSeries.coe_substAlgHom hb, map_mul, map_sub,
    MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  rfl
end Formalism.L2.Th1.B.E2
