-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.Ucol_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:09:17.535799+00:00
-- url     : https://prove2.me/submissions/ee60ba87-ab5c-487c-a805-babc676c214e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
import Theorems.Thm_ClauseBound_ParityChecks_Num_frac
import Theorems.Thm_ClauseBound_ParityChecks_Num_sum_col

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution (hnb : 1 ≤ q.nb) (hm : 1 ≤ q.m) {Ls : List Chk} (cur : Chk) (e : ℕ) (hj : Ls.length < q.r) :
    Ucol q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) = (q.numC Ls cur e : ℚ) / (8 * q.m * ((q.nb : ℚ) + 1) ^ q.r) := by
  have h1 : (q.m : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.m ≠ 0)
  have h3 : ((q.nb : ℚ) + 1) ^ q.r ≠ 0 := by positivity
  unfold Ucol
  rw [Fintype.card_fin, Finset.sum_congr rfl fun x _ => frac q.nb _ _ q.r hnb (Nat.sub_le _ _), ← Finset.sum_div, ← Nat.cast_sum,
    sum_col cur e hj]
  field_simp
end ClauseBound.ParityChecks.Num
