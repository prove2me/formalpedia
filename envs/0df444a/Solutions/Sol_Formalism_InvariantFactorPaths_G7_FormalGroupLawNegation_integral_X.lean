-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLawNegation.integral_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:04:21.884659+00:00
-- url     : https://prove2.me/submissions/0eac831d-9cb3-47ec-9fa3-7ee0d1406271

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_KOneConsequenceOf

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
open Formalism.InvariantFactorPaths.G7.FormalGroupLawNegation
open FormalGroupLaws
namespace Formalism.InvariantFactorPaths.G7.FormalGroupLawNegation
theorem _root_.solution {K ι : Type} [NormedField K] (x : ι) :
    Integral (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp
end Formalism.InvariantFactorPaths.G7.FormalGroupLawNegation
