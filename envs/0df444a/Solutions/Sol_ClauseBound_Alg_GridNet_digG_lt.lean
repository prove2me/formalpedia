-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.digG_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:43:18.361117+00:00
-- url     : https://prove2.me/submissions/cbcef18b-5c10-410d-9aca-6bc6bcad13e8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_Groundwork_Grid_digit_le
import Theorems.Thm_Groundwork_Prog_digit_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {P : PiecesF} {pad : U} {h ℓ : ℕ} {A : ℕ → Pieces.Four ℓ}
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (hP : 1 ≤ P.cnt h ℓ) (d : ℕ) (tr : Bool) (y q κ : ℕ) : digG P d tr h ℓ y q κ < P.cnt h ℓ := by
  have := Prog.digit_le (P.cnt h ℓ - 1) y (rectIxG d tr q κ)
  unfold digG
  omega
end ClauseBound.Alg.GridNet
