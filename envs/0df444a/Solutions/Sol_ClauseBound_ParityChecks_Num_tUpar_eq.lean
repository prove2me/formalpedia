-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.tUpar_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:03:23.703885+00:00
-- url     : https://prove2.me/submissions/ec270b44-ea2b-4285-b814-c766700c520e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
import Theorems.Thm_ClauseBound_ParityChecks_Num_numP_cast
import Theorems.Thm_ClauseBound_ParityChecks_Approx_compute


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution (hnb : 1 ≤ q.nb) (j : ℕ) (Λ : ℕ → Finset (Fin q.m)) (D : Finset (Fin q.m)) :
    tUpar V q.nb q.r q.i₀ j Λ D =
      (5 / 8) ^ q.k j * (1 / 2) * ((q.numP (Aint V q.nb j Λ) (fun i => Bint V q.nb i j Λ D) : ℚ) / (q.nb : ℚ) ^ q.i₀) := by
  have h0 : (q.nb : ℚ) ^ q.i₀ ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q.nb ≠ 0))
  rw [Approx.compute, numP_cast hnb, mul_div_cancel_left₀ _ h0]
  rfl
end ClauseBound.ParityChecks.Num
