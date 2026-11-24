-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.pow_mod_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:57:21.0261+00:00
-- url     : https://prove2.me/submissions/b629a389-b524-4bc1-a8b6-4ef294877a5f

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
theorem _root_.solution {K : Type*} [Monoid K] {w : K} {N : ℕ} (hw : w ^ N = 1) (a : ℕ) :
    w ^ (a % N) = w ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hw, one_pow, mul_one]
end Formalism.FrobeniusOrbits.Cond
