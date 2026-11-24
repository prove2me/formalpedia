-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.subst2_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:41:40.209981+00:00
-- url     : https://prove2.me/submissions/768f71be-6a88-40da-a3b7-7601cead7f74

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_hs2
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs2


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
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.Pair
theorem _root_.solution {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    {a b : MvPowerSeries ι K} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (f : MvPowerSeries (Fin 2) K) :
    subst φ (subst ![a, b] f) = subst ![subst φ a, subst φ b] f := by
  rw [subst_comp_subst_apply (hs2 ha hb) hφ]
  congr 1
  funext i
  fin_cases i <;> rfl
end Formalism.L2.Th1.D.Pair
