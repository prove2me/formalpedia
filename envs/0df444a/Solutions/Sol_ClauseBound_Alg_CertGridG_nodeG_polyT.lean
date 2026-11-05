-- Prove2me | solution 1 for ClauseBound.Alg.CertGridG.nodeG_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:14:39.468925+00:00
-- url     : https://prove2.me/submissions/fed86a18-3067-44cd-98f5-980ac98dd22a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.Alg.CertGridG
theorem _root_.solution {d a i : α → ℕ} {tr : α → Bool} (hd : PolyT d) (ht : PolyT tr) (ha : PolyT a) (hi : PolyT i) :
    PolyT fun x => nodeG (d x) (tr x) (a x) (i x) :=
  PolyT.ite' (PolyT.decide_eq_true ht) (ha.add (hd.mul hi)) (hi.add (hd.mul ha))
end ClauseBound.Alg.CertGridG
