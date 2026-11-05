-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.Inv.lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:23:11.326978+00:00
-- url     : https://prove2.me/submissions/f42747c5-89ac-4e1e-814e-72e894e38c1b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
import Theorems.Thm_ClauseBound_ParityChecks_Run_NN_nonneg
import Theorems.Thm_ClauseBound_ParityChecks_Run_eps_nonneg

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
variable {q}
variable {V} {orcA orcB} {ε : ℚ}
namespace ClauseBound.ParityChecks.Run
namespace Inv
theorem _root_.solution (hq : Hyp q (Fintype.card X) ε) {Ls : List Chk} {cur : Chk} {e : ℕ} (h : Inv q V ε Ls cur e) : UU q V Ls cur e < 1 := by
  have h1 : Ls.length * q.m + e ≤ q.m * q.r := by
    have h2 : (Ls.length + 1) * q.m ≤ q.r * q.m := Nat.mul_le_mul_right _ h.lt
    have := h.le
    nlinarith
  have h3 : ((Ls.length * q.m + e : ℕ) : ℚ) ≤ (q.m : ℚ) * q.r := by exact_mod_cast h1
  have h4 : 0 ≤ ε * NN X q := mul_nonneg (eps_nonneg hq) NN_nonneg
  have h5 := mul_le_mul_of_nonneg_right h3 h4
  have h6 : ε * NN X q * ((q.m : ℚ) * q.r) < 1 / 4 := hq.drift
  have := h.pot
  linarith
end Inv
end ClauseBound.ParityChecks.Run
