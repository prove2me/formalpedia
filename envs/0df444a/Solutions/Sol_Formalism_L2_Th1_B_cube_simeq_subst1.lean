-- Prove2me | solution 1 for Formalism.L2.Th1.B.cube_simeq_subst1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:25.695325+00:00
-- url     : https://prove2.me/submissions/7a46c4a0-75ac-47e4-9ca6-ad5cb1ab3af5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffEqZeroOfParallelogram
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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution {f g : PowerSeries K} (hq : Simeq (ι := Unit) f g)
    (U : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0) (iU : Integral U) :
    Simeq (PowerSeries.subst U f) (PowerSeries.subst U g) :=
  (equivalence_rules K Unit).2.2.2.2 ι f g (fun _ => U) (fun _ => hU) (fun _ => iU) hq
end Formalism.L2.Th1.B
