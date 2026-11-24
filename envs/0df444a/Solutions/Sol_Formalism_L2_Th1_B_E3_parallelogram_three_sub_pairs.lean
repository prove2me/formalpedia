-- Prove2me | solution 1 for Formalism.L2.Th1.B.E3.parallelogram_three_sub_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:04:14.326842+00:00
-- url     : https://prove2.me/submissions/15511b9f-164c-4ef3-81e3-493844d9db74

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_FirstLevelOfThreeVarParallelogram
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_Formalism_L2_Th1_B_cube_par_subst
import Theorems.Thm_Formalism_L2_Th1_B_parallelogram_coboundary_three_vars


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E3
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
namespace Formalism.L2.Th1.B.E3
theorem _root_.solution {K : Type} [NormedField K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (hF : MvPowerSeries.constantCoeff F = 0) (i f : PowerSeries K)
    (hi : PowerSeries.constantCoeff i = 0) :
    par3 F i f -
        MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1]
          (par F i f) -
        MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]
          (par F i f) -
        MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]
          (par F i f) =
      d1 F (cob F f) := by
  have h0 : ∀ j : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  rw [parallelogram_coboundary_three_vars F hF f, cube_par_subst F hF i f hi _ _ (h0 0) (h0 1),
    cube_par_subst F hF i f hi _ _ (h0 0) (h0 2), cube_par_subst F hF i f hi _ _ (h0 1) (h0 2)]
  unfold par3 F3 lawDifferenceThree in3 at1
  ring
end Formalism.L2.Th1.B.E3
