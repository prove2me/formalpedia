-- Prove2me | solution 1 for ClauseBound.Alg.CertLevel.nRectG_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:23:59.423199+00:00
-- url     : https://prove2.me/submissions/aa0479ef-ba42-423c-a32d-78126443262a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_ClauseBound_Alg_CertLevel_p_unary
import Theorems.Thm_ClauseBound_Alg_CertLevel_d_unary
import Theorems.Thm_ClauseBound_Alg_CertLevel_c2_unary
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_mul
attribute [local fun_prop] Groundwork.PolyT.mul



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}
namespace ClauseBound.Alg.CertLevel
theorem _root_.solution {s : α → Step} (hs : PolyT s) : Unary fun x => nRectG (s x).p (s x).d :=
  (c2_unary (p_unary hs)).mul (c2_unary (d_unary hs))
end ClauseBound.Alg.CertLevel
