-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.Urow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:07:30.360651+00:00
-- url     : https://prove2.me/submissions/98427a66-c166-451b-b9cc-0331a8a8378e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
import Theorems.Thm_ClauseBound_ParityChecks_Num_frac
import Theorems.Thm_ClauseBound_ParityChecks_Num_sum_row

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution (hnb : 1 ≤ q.nb) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r)
    (hall : ∀ L ∈ Ls ++ [cur], ChkOK q.m L) (he : e ≤ q.m) :
    Urow q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) = (q.numR Ls cur e : ℚ) / (8 * q.r * ((q.nb : ℚ) + 1) ^ q.m) := by
  have h2 : (q.r : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.r ≠ 0)
  have h3 : ((q.nb : ℚ) + 1) ^ q.m ≠ 0 := by positivity
  unfold Urow
  rw [Fintype.card_fin, Finset.sum_congr rfl fun j' _ => frac q.nb _ _ q.m hnb (Nat.sub_le _ _), ← Finset.sum_div, ← Nat.cast_sum,
    sum_row hj hall he]
  field_simp
end ClauseBound.ParityChecks.Num
