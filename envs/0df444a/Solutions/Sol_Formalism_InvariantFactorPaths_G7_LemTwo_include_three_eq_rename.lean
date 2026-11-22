-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.include_three_eq_rename
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:02.959972+00:00
-- url     : https://prove2.me/submissions/80234ab9-7c0b-4f88-a276-7c3ae29c6951

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf

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
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemTwo
theorem _root_.solution (g : MvPowerSeries (Fin 2) K) :
    in3 g = MvPowerSeries.rename (Fin.castSuccEmb (n := 2)) g := by
  rw [MvPowerSeries.rename_eq_subst, in3]
  congr 1
  funext i
  fin_cases i <;> rfl
end Formalism.InvariantFactorPaths.G7.LemTwo
