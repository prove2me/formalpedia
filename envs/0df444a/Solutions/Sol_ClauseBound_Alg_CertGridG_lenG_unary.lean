-- Prove2me | solution 1 for ClauseBound.Alg.CertGridG.lenG_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:51:24.658215+00:00
-- url     : https://prove2.me/submissions/4d31c4c8-f2a4-4225-b33a-27f074a354e1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG
import Theorems.Thm_ClauseBound_Alg_CertGridG_cap_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_digG_polyT

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]
variable {P : PiecesF} (K : P.Keeps)
include K
namespace ClauseBound.Alg.CertGridG
theorem _root_.solution {d h ℓ y q κ : α → ℕ} {tr : α → Bool} (hd : PolyT d) (ht : PolyT tr) (hh : Unary h) (hℓ : Unary ℓ) (hy : PolyT y) (hq : PolyT q)
    (hκ : PolyT κ) : Unary fun x => lenG P (d x) (tr x) (h x) (ℓ x) (y x) (q x) (κ x) :=
  cap_unary K ht hh hℓ (digG_polyT K hd ht hh hℓ hy hq hκ)
end ClauseBound.Alg.CertGridG
