-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.ringChar_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:55:53.294492+00:00
-- url     : https://prove2.me/submissions/0eaf86fc-5c32-46b7-8696-b44055e8f802

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
variable {K : Type*} [Field K] [CharZero K]
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  intro h
  omega
end Formalism.FrobeniusOrbits.Cond
