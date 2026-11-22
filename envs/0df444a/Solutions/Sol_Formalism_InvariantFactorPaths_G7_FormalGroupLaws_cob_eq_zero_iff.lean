-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.cob_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:03.120143+00:00
-- url     : https://prove2.me/submissions/6fb0c0ad-85f3-4be7-8830-915e7438ddaa

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne

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
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.FormalGroupLaws
theorem _root_.solution (F : MvPowerSeries (Fin 2) K) (f : PowerSeries K) :
    cob F f = 0 ↔ PowerSeries.subst F f = at1 0 f + at1 1 f := by
  rw [cob, sub_sub, sub_eq_zero]
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
