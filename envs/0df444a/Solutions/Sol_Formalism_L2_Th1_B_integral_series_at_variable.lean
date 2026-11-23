-- Prove2me | solution 1 for Formalism.L2.Th1.B.integral_series_at_variable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:30.130743+00:00
-- url     : https://prove2.me/submissions/e3b3c620-a346-428b-8b10-444143b90324

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_IntegralInverse
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Theorems.Thm_Formalism_L2_Th1_B_law_integral_X
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
theorem _root_.solution [IsUltrametricDist K] {ι : Type} (x : ι) (f : PowerSeries K)
    (hf : Integral (ι := Unit) f) : Integral (at1 x f) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (φ := fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries ι K))
    (fun _ => by simp) (fun _ => law_integral_X x) hf
end Formalism.L2.Th1.B
