-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLawNegation.integral_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:10:26.829816+00:00
-- url     : https://prove2.me/submissions/fa8ae4b4-e0db-4c57-ad74-ab07726ca3eb

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
theorem _root_.solution {K ι : Type} [NormedField K] {f : MvPowerSeries ι K} (hf : Integral f) :
    Integral (-f) := by
  intro n
  rw [map_neg, norm_neg]
  exact hf n
end Formalism.InvariantFactorPaths.G7.FormalGroupLawNegation
