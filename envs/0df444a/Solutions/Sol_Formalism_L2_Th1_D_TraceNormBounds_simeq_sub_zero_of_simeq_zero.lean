-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.simeq_sub_zero_of_simeq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:39.051869+00:00
-- url     : https://prove2.me/submissions/2b94c2be-dff7-4626-9ce7-93efba79f938

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open MvPowerSeries
open Formalism.L2.Th1.D.TraceNormBounds
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.L2.Th1.D.TraceNormBounds
theorem _root_.solution {τ : Type} {f g : MvPowerSeries τ K} (hf : Simeq f 0) (hg : Simeq g 0) :
    Simeq (f - g) 0 := by
  have hS : Formalism.InvariantFactorPaths.G7.SimeqRules := Formalism.InvariantFactorPaths.G7.equivalence_rules
  have h1 := (hS K τ).2.2.1 f 0 g hf ((hS K τ).2.1 g 0 hg)
  unfold Simeq at h1 ⊢
  rw [sub_zero]
  exact h1
end Formalism.L2.Th1.D.TraceNormBounds
