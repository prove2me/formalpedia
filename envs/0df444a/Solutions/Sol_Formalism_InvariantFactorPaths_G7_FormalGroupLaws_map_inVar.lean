-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_inVar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:41.933858+00:00
-- url     : https://prove2.me/submissions/c96b33c3-8fea-4116-9fac-1d395b556bd2

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
theorem _root_.solution {L ι : Type} [Field L] (φ : K →+* L) (x : ι) (f : PowerSeries K) :
    MvPowerSeries.map φ (at1 x f) = at1 x (PowerSeries.map φ f) := by
  rw [at1, at1, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)),
    MvPowerSeries.map_X]
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
