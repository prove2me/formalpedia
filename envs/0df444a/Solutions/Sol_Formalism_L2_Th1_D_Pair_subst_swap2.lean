-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.subst_swap2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:22.807209+00:00
-- url     : https://prove2.me/submissions/9ef75021-581d-452e-b8f6-af1acfaab83f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_hs2
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst2_comp
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
theorem _root_.solution {τ : Type} {a b : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (H : MvPowerSeries (Fin 2) K) :
    subst ![a, b] (swap2 H) = subst ![b, a] H := by
  have h2 := hs2 ha hb
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  unfold swap2
  rw [subst2_comp h2 (hX 1) (hX 0)]
  simp only [subst_X h2]
  first | rfl | simp
end Formalism.L2.Th1.D.Pair
