-- Prove2me | solution 1 for Formalism.L2.Th1.B.parallelogram_coboundary_three_vars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:22:06.112801+00:00
-- url     : https://prove2.me/submissions/15b9b304-935d-4695-acce-8ddb616ce4ca

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffEqZeroOfParallelogram
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_subst_two_variables
import Theorems.Thm_Formalism_L2_Th1_B_cube_cob_subst
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 subst2_subst psubst_subst psubst_injective subst_zero')
variable {K : Type} [NormedField K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) :
    d1 F (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![MvPowerSeries.subst
          ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] F,
          MvPowerSeries.X 2] F) f -
        PowerSeries.subst (MvPowerSeries.subst
          ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] F) f -
        PowerSeries.subst (MvPowerSeries.subst
          ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] F) f -
        PowerSeries.subst (MvPowerSeries.subst
          ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] F) f +
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) f +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) f +
        PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f := by
  unfold d1 in3
  rw [cube_cob_subst F hF f _ _ (constantCoeff_subst_two_variables F hF _ _ (by simp) (by simp)) (by simp),
    cube_cob_subst F hF f _ _ (by simp) (by simp), cube_cob_subst F hF f _ _ (by simp) (by simp)]
  ring
end Formalism.L2.Th1.B
