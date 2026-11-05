-- Prove2me | solution 1 for ClauseBound.Alg.CertGridG.nParts_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:15:01.22438+00:00
-- url     : https://prove2.me/submissions/2e9ddae9-a8a4-4867-a156-d55b56838b05

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.Alg.CertGridG
theorem _root_.solution {p d : α → ℕ} {tr : α → Bool} (hp : PolyT p) (hd : PolyT d) (ht : PolyT tr) :
    PolyT fun x => nParts (p x) (d x) (tr x) :=
  PolyT.ite' (PolyT.decide_eq_true ht) hd hp
end ClauseBound.Alg.CertGridG
