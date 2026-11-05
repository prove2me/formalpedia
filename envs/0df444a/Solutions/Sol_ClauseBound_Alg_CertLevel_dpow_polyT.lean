-- Prove2me | solution 1 for ClauseBound.Alg.CertLevel.dpow_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:10:32.959482+00:00
-- url     : https://prove2.me/submissions/b0e7c918-0478-4665-a23e-acdf52a32022

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_ClauseBound_Alg_CertLevel_nRectG_unary
import Theorems.Thm_ClauseBound_Alg_CertLevel_d_polyT
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_pow_unary
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}
variable (hP : P.Keeps)
include hP
namespace ClauseBound.Alg.CertLevel
theorem _root_.solution {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) :
    PolyT fun x => P.d (s x).h (l x).length ^ nRectG (s x).p (s x).d :=
  PolyT.pow_unary (d_polyT hP hs hl) (nRectG_unary hs)
end ClauseBound.Alg.CertLevel
