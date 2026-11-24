-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.swap_two_eq_rename
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.699876+00:00
-- url     : https://prove2.me/submissions/dc70bb6f-3bbc-452a-a464-5dcf87eb6fc9

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
theorem _root_.solution (H : MvPowerSeries (Fin 2) K) :
    swap2 H = MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1).toEmbedding H := by
  rw [MvPowerSeries.rename_eq_subst, swap2]
  congr 1
  funext i
  fin_cases i <;> rfl
end Formalism.InvariantFactorPaths.G7.LemTwo
