-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.degree_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:45.595478+00:00
-- url     : https://prove2.me/submissions/b1818477-1bd7-4034-bc5d-aae5307be6e2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul

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
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution (i j : ℕ) :
    (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j).degree = i + j := by
  rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
end Formalism.InvariantFactorPaths.G7.LemOne
