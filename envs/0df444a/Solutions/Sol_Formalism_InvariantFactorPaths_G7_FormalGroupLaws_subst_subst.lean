-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.subst_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:55.385805+00:00
-- url     : https://prove2.me/submissions/732234b4-e4bc-446d-8e8e-38a7f87e71f7

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
theorem _root_.solution {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : MvPowerSeries.HasSubst b)
    {a : MvPowerSeries ι K} (ha : PowerSeries.HasSubst a) (f : PowerSeries K) :
    MvPowerSeries.subst b (PowerSeries.subst a f) =
      PowerSeries.subst (MvPowerSeries.subst b a) f := by
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const ha) hb]
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
