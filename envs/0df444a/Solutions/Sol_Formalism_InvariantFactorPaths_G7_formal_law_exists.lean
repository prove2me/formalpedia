-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.formal_law_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:27:24.007162+00:00
-- url     : https://prove2.me/submissions/03cdcd75-09e2-4dae-895a-f65bf12c1f7d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_law_exists
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_law_unique
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_law_integral

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
open FormalGroupLaws
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : LawExists := by
  intro K _ _ _ p hp hnp
  refine ⟨?_, fun F F' h0 h0' h h' => law_unique p hp.two_le F F' h0 h0' h h'⟩
  obtain ⟨F, hF0, hF⟩ := law_exists (K := K) p hp.two_le
  exact ⟨F, hF0, law_integral p hp hnp F hF0 hF, hF⟩
end Formalism.InvariantFactorPaths.G7
