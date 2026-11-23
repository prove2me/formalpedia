-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.subst_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:30.861388+00:00
-- url     : https://prove2.me/submissions/19fa98a1-3429-46d0-96f8-3daf4b805cac

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
theorem _root_.solution {τ : Type} {G : MvPowerSeries (Fin 2) K} (hG : DivAB G)
    {w : MvPowerSeries τ K} (hw : constantCoeff w = 0) : subst ![0, w] G = 0 := by
  have hd : (X 0 : MvPowerSeries (Fin 2) K) ∣ G := X_dvd_iff.2 fun m hm => hG m (Or.inl hm)
  obtain ⟨Q, rfl⟩ := hd
  have h := hs2 (map_zero _) hw
  rw [subst_mul h, subst_X h]
  simp
end Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
