-- Prove2me | solution 1 for ClauseBound.Alg.CertLevel.sqrt_eq_countP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:41.401305+00:00
-- url     : https://prove2.me/submissions/7e9d388d-ec8d-4cc0-b754-979aded2935d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_ClauseBound_Alg_CertLevel_countP_le_range
import Theorems.Thm_Groundwork_PolyT_countP
attribute [local fun_prop] Groundwork.PolyT.countP



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}
namespace ClauseBound.Alg.CertLevel
theorem _root_.solution (n : ℕ) : Nat.sqrt n = (List.range (n + 1)).countP (fun r => decide (r * r ≤ n)) - 1 := by
  have h : (fun r => decide (r * r ≤ n)) = fun r => decide (r ≤ Nat.sqrt n) := by
    funext r
    exact decide_eq_decide.2 Nat.le_sqrt.symm
  have h2 := Nat.sqrt_le_self n
  rw [h, countP_le_range]
  omega
end ClauseBound.Alg.CertLevel
