-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.chi_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:21:25.427046+00:00
-- url     : https://prove2.me/submissions/95f4565b-9135-4771-a6ed-75590fdb392e

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_ringChar_ne_two

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
theorem _root_.solution {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) : chi p K (-1) = -1 := by
  have h := quadraticChar_neg_one (ringChar_ne_two hp4)
  simp only [chi, MulChar.ringHomComp_apply, h, ZMod.card]
  rw [ZMod.χ₄_nat_three_mod_four hp4]
  simp
end Formalism.FrobeniusOrbits.Cond
