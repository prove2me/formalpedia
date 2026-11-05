-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.Uinc_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:07:10.113938+00:00
-- url     : https://prove2.me/submissions/e6b565b1-a99e-4e8b-9029-ebe58555639f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
import Theorems.Thm_ClauseBound_ParityChecks_Num_sum_card
import Theorems.Thm_ClauseBound_ParityChecks_Num_sum_undRow

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution (hnb : 1 ≤ q.nb) (hm : 1 ≤ q.m) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r)
    (hall : ∀ L ∈ Ls ++ [cur], ChkOK q.m L) :
    Uinc q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) = (q.numI Ls cur e : ℚ) / (8 * q.m * q.r) := by
  have h0 : (q.nb : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.nb ≠ 0)
  have h1 : (q.m : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.m ≠ 0)
  have h2 : (q.r : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.r ≠ 0)
  unfold Uinc Par.numI Par.k
  rw [sum_card hall hj, sum_undRow _ _ hj, Fintype.card_fin]
  generalize (Ls.map List.length).sum + cur.length = I
  generalize q.m - e + (q.r - 1 - Ls.length) * q.m = Und
  unfold pr
  push_cast
  field_simp
end ClauseBound.ParityChecks.Num
