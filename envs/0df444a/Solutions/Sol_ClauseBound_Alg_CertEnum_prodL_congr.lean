-- Prove2me | solution 1 for ClauseBound.Alg.CertEnum.prodL_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:40:01.792423+00:00
-- url     : https://prove2.me/submissions/8cd684af-a901-44a6-8bd6-ffcd5e98659a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertEnum
import Theorems.Thm_PaddedDescent_F_prodL_eq


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertEnum
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertNet
variable {α : Type} [Enc α] {C : Type} [Enc C] {F : FNet C}
namespace ClauseBound.Alg.CertEnum
theorem _root_.solution {n : ℕ} {f f' : ℕ → ℤ} (h : ∀ y < n, f y = f' y) : prodL n f = prodL n f' := by
  rw [prodL_eq, prodL_eq]
  exact Finset.prod_congr rfl fun y hy => h y (Finset.mem_range.1 hy)
end ClauseBound.Alg.CertEnum
