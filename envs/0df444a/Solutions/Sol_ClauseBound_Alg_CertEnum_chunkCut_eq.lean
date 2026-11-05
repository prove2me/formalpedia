-- Prove2me | solution 1 for ClauseBound.Alg.CertEnum.chunkCut_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:40:04.713073+00:00
-- url     : https://prove2.me/submissions/905e591e-9a9f-4354-a4ca-467f1741e46b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertEnum
import Theorems.Thm_Groundwork_sum_range_eq_list


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertEnum
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertNet
variable {α : Type} [Enc α] {C : Type} [Enc C] {F : FNet C}
omit [Enc C]
namespace ClauseBound.Alg.CertEnum
theorem _root_.solution {g : ℕ} (F : FNet C) (c : C) {j : ℕ} (hj : j ≤ g * g) (w : List Bool) :
    chunkCut g F c j w = chunkAt (enumLen g F c) j w := by
  rw [chunkCut, chunkAt, min_eq_left hj, sum_range_eq_list]
end ClauseBound.Alg.CertEnum
