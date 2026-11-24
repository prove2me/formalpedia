-- Prove2me | solution 1 for Formalism.MainNotions.J.map_pI_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:42:47.28585+00:00
-- url     : https://prove2.me/submissions/18c9b5c7-5ffc-4ff9-9ad1-964caa12dbd2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open Ideal NumberField IsDedekindDomain
variable (K : Type) [Field K] [NumberField K] (p : ℕ)
namespace Formalism.MainNotions.J
theorem _root_.solution (hp : p.Prime) : map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) ≠ ⊥ := by
  rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot, map_natCast]
  exact_mod_cast hp.ne_zero
end Formalism.MainNotions.J
