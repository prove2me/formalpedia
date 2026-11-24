-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.eq_zero_of_neg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:19:17.196081+00:00
-- url     : https://prove2.me/submissions/5a876897-38dc-4243-8842-911354c4a744

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution {K : Type*} [Field K] [CharZero K] {g : K} (h : -g = g) : g = 0 := by
  have h2 : (2 : K) * g = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact h3
end Formalism.FrobeniusOrbits.Cond
