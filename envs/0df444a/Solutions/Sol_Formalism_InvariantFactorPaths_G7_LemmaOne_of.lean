-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemmaOne_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:42:30.573496+00:00
-- url     : https://prove2.me/submissions/cd6569ea-c0b5-4296-9c51-c34060f8cb71

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_exists_limit

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
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hDe : DeIntegral) (hL : LawSymm) : LemmaOne := by
  intro K _ _ _ _ p σ hU F hF f hf0 hcob
  obtain ⟨hp, -, hnp, -, hσ⟩ := hU
  have hde := hDe K p σ hp hnp hσ F hF
  have hF1 := (hL K p hp hnp F hF).2.2.1
  obtain ⟨hF0, hFi, hFl⟩ := hF
  obtain ⟨a, b, ha, hR⟩ := LemOne.exists_limit hp hnp hF0 hFi hF1 hFl hde hf0 hcob
  refine ⟨a, b, LemOne.rem p f a b, ha, hR, ?_⟩
  unfold LemOne.rem
  ring
end Formalism.InvariantFactorPaths.G7
