-- Prove2me | solution 1 for Formalism.L2.Th1.B.law_integral_FI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:04.674879+00:00
-- url     : https://prove2.me/submissions/07587f6d-1420-4a96-a333-61d42957eb4a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_IntegralInverse
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Theorems.Thm_Formalism_L2_Th1_B_law_integral_X
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_series_at_variable
import Theorems.Thm_Formalism_L2_Th1_B_integral_series_at_variable
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_subst__564f1f6f92b9


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
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G.LogP (hs2 subst2_subst psubst_subst psubst_injective)
variable {K : Type} [NormedField K]
namespace Formalism.L2.Th1.B
theorem _root_.solution [IsUltrametricDist K] {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K}
    (h : LawLog F l) (hi : IsInv l i) : Integral (FI F i) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst'
    (fun k => by
      fin_cases k
      · exact MvPowerSeries.constantCoeff_X 0
      · exact constantCoeff_series_at_variable 1 i hi.1)
    (fun k => by
      fin_cases k
      · exact law_integral_X 0
      · exact integral_series_at_variable 1 i hi.2.1) h.2.1
end Formalism.L2.Th1.B
