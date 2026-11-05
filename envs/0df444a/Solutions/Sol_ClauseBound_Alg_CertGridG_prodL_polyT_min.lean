-- Prove2me | solution 1 for ClauseBound.Alg.CertGridG.prodL_polyT_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:33.394602+00:00
-- url     : https://prove2.me/submissions/72e4d499-c105-4799-ae3c-48a4f122d877

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG
import Theorems.Thm_ClauseBound_Alg_CertGridG_prodL_min
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.Alg.CertGridG
theorem _root_.solution {n : α → ℕ} {f : α → ℕ → ℤ} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => prodL (n x) (f x) :=
  (prodL_polyT (f := fun x j => f x (min j (n x))) hn hf).congr fun _ => prodL_min _ _
end ClauseBound.Alg.CertGridG
