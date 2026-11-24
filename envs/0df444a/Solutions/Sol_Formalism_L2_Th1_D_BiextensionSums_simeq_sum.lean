-- Prove2me | solution 1 for Formalism.L2.Th1.D.BiextensionSums.simeq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:38:59.643807+00:00
-- url     : https://prove2.me/submissions/f3fbabc8-8059-475d-b089-5cf9b33085be

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_simeqRules
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_simeqRules


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionSums
namespace Formalism.L2.Th1.D.BiextensionSums
theorem _root_.solution {K ι α : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
    (s : Finset α) (f g : α → MvPowerSeries ι K) (h : ∀ a ∈ s, Simeq (f a) (g a)) :
    Simeq (∑ a ∈ s, f a) (∑ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).1 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).2.2.2.1 _ _ _ _ (h a (Finset.mem_insert_self _ _))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
end Formalism.L2.Th1.D.BiextensionSums
