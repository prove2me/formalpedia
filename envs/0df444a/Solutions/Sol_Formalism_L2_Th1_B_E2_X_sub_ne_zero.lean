-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.X_sub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:18.580595+00:00
-- url     : https://prove2.me/submissions/7e2a7528-3c77-4de4-aee4-593a20e21045

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
variable {K : Type} [NormedField K] [CharZero K]
namespace Formalism.L2.Th1.B.E2
theorem _root_.solution {j k : Fin 3} (h : j ≠ k) :
    (MvPowerSeries.X j - MvPowerSeries.X k : MvPowerSeries (Fin 3) K) ≠ 0 := by
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) h0
  rw [map_sub, map_zero, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl,
    if_neg (fun hh => h (Finsupp.single_left_injective one_ne_zero hh))] at h1
  simp at h1
end Formalism.L2.Th1.B.E2
