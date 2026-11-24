-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.pow_congr_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:25:57.766632+00:00
-- url     : https://prove2.me/submissions/50bd0807-0fa4-46fb-8750-b408cef47760

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_pow_mod_of

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
theorem _root_.solution {K : Type*} [Monoid K] {w : K} {N : ℕ} (hw : w ^ N = 1) {a b : ℕ}
    (h : a % N = b % N) : w ^ a = w ^ b := by
  rw [← pow_mod_of hw a, ← pow_mod_of hw b, h]
end Formalism.FrobeniusOrbits.Cond
