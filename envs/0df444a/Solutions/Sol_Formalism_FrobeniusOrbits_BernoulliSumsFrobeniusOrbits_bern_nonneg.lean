-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits.bern_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:22.958844+00:00
-- url     : https://prove2.me/submissions/a8f1fd76-f920-494d-84ec-46e98e774e71

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits
variable {α : Type*} [Fintype α]
namespace Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits
theorem _root_.solution {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) : 0 ≤ bern δ T := by
  unfold bern
  have : 0 ≤ 1 - δ := by linarith
  positivity
end Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits
