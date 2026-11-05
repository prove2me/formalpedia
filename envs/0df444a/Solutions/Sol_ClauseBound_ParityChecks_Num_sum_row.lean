-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.sum_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:04:27.524229+00:00
-- url     : https://prove2.me/submissions/96f29cde-aeeb-4711-bd54-b9f2749dd3cd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
import Theorems.Thm_ClauseBound_ParityChecks_Num_sum_getD
import Theorems.Thm_ClauseBound_ParityChecks_Num_sum_split
import Theorems.Thm_ClauseBound_ParityChecks_Num_getD_mid
import Theorems.Thm_ClauseBound_ParityChecks_Num_getD_late
import Theorems.Thm_ClauseBound_ParityChecks_card_lam
import Theorems.Thm_ClauseBound_ParityChecks_Num_undRow_early
import Theorems.Thm_ClauseBound_ParityChecks_Num_undRow_mid
import Theorems.Thm_ClauseBound_ParityChecks_Num_undRow_late

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r) (hall : ∀ L ∈ Ls ++ [cur], ChkOK q.m L) (he : e ≤ q.m) :
    ∑ j' ∈ range q.r, 2 ^ #(lam q.m (Ls ++ [cur]) j') * q.nb ^ (q.m - undRow Ls.length (Dset q.m e) j') *
      (q.nb + 1) ^ (q.m - (q.m - undRow Ls.length (Dset q.m e) j')) = q.numR Ls cur e := by
  simp_rw [card_lam q hall]
  rw [sum_split _ hj, undRow_mid, getD_mid, Nat.sub_sub_self he]
  have h1 : ∑ i ∈ range Ls.length, 2 ^ ((Ls ++ [cur]).getD i []).length * q.nb ^ (q.m - undRow Ls.length (Dset q.m e) i) *
      (q.nb + 1) ^ (q.m - (q.m - undRow Ls.length (Dset q.m e) i)) = (Ls.map fun L => 2 ^ L.length * q.nb ^ q.m).sum := by
    rw [← sum_getD (fun L => 2 ^ L.length * q.nb ^ q.m) Ls [cur]]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [undRow_early (mem_range.1 hi)]
    simp
  rw [h1]
  simp only [undRow_late, getD_late, List.length_nil, pow_zero, Nat.sub_self, Nat.sub_zero, one_mul, sum_const, card_range, smul_eq_mul]
  rfl
end ClauseBound.ParityChecks.Num
