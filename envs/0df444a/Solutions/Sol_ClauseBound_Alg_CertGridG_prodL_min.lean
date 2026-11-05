-- Prove2me | solution 1 for ClauseBound.Alg.CertGridG.prodL_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:10:19.379718+00:00
-- url     : https://prove2.me/submissions/d02780bf-1853-4dfe-9bf4-b75f9257daa6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG
import Theorems.Thm_PaddedDescent_F_prodL_eq


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.Alg.CertGridG
theorem _root_.solution (n : ℕ) (f : ℕ → ℤ) : prodL n (fun j => f (min j n)) = prodL n f := by
  rw [prodL_eq, prodL_eq]
  exact Finset.prod_congr rfl fun j hj => by rw [min_eq_left (Finset.mem_range.1 hj).le]
end ClauseBound.Alg.CertGridG
