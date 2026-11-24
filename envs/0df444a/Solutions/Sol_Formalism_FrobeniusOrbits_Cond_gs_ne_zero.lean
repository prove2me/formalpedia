-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.gs_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:06:03.662606+00:00
-- url     : https://prove2.me/submissions/7fee8ab4-f70e-470c-bbca-40e57c40dc48

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_gs_sq

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
theorem _root_.solution {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) {x : K} (hx : IsPrimitiveRoot x p) :
    gs p hx.pow_eq_one ≠ 0 := by
  intro h
  have h2 := gs_sq (K := K) hp4 hx
  rw [h] at h2
  have hp : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact hp (by linear_combination h2)
end Formalism.FrobeniusOrbits.Cond
