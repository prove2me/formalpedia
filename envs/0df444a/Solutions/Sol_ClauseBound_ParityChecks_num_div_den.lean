-- Prove2me | solution 1 for ClauseBound.ParityChecks.num_div_den
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:10:32.129503+00:00
-- url     : https://prove2.me/submissions/4ceac976-2647-4cc5-89a9-c0f41620d25a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
import Theorems.Thm_ClauseBound_ParityChecks_Num_all_ok
import Theorems.Thm_ClauseBound_ParityChecks_Num_Uinc_eq
import Theorems.Thm_ClauseBound_ParityChecks_Num_Urow_eq
import Theorems.Thm_ClauseBound_ParityChecks_Num_Ucol_eq
import Theorems.Thm_ClauseBound_ParityChecks_Num_tUpar_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
namespace ClauseBound.ParityChecks
theorem _root_.solution (hnb : 1 ≤ q.nb) (hm : 1 ≤ q.m) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r) (hL : ∀ L ∈ Ls, ChkOK q.m L)
    (hc : ChkOK e cur) (he : e ≤ q.m) :
    (q.num (Aint V q.nb Ls.length (lam q.m (Ls ++ [cur]))) (fun i => Bint V q.nb i Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)) Ls cur e : ℚ) / q.den Ls.length
      = tUpar V q.nb q.r q.i₀ Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) + Uinc q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)
        + Urow q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) + Ucol q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) := by
  have hall := Num.all_ok hL hc he
  have h0 : (q.nb : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.nb ≠ 0)
  have h1 : (q.m : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.m ≠ 0)
  have h2 : (q.r : ℚ) ≠ 0 := by exact_mod_cast (by omega : q.r ≠ 0)
  have h3 : (q.nb : ℚ) + 1 ≠ 0 := by positivity
  rw [Num.tUpar_eq V hnb, Num.Uinc_eq hnb hm hj hall, Num.Urow_eq hnb hj hall he, Num.Ucol_eq hnb hm cur e hj]
  unfold Par.num Par.den
  generalize q.numP _ _ = nP
  generalize q.numI Ls cur e = nI
  generalize q.numR Ls cur e = nR
  generalize q.numC Ls cur e = nC
  generalize q.k Ls.length = k
  push_cast
  rw [div_pow, pow_add]
  field_simp
  ring
end ClauseBound.ParityChecks
