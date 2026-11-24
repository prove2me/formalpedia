-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.sqrt_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:59:54.595127+00:00
-- url     : https://prove2.me/submissions/fde5bd0b-2d25-40a3-80bc-68700466af5b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_gs_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_prim_pow

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
theorem _root_.solution {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) {N : ℕ} [NeZero N] (hp : p ∣ N) :
    ∃ g : Cyc N, g ^ 2 = -(p : Cyc N) := by
  exact ⟨_, gs_sq hp4 (prim_pow hp)⟩
end Formalism.FrobeniusOrbits.Cond
