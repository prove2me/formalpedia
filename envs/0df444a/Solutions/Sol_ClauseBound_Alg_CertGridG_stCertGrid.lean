-- Prove2me | solution 1 for ClauseBound.Alg.CertGridG.stCertGrid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:17:39.682208+00:00
-- url     : https://prove2.me/submissions/473b9896-884e-46e9-82b4-571c65d48150

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG
import Theorems.Thm_ClauseBound_Alg_CertGridG_gridF_keeps

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.Alg.CertGridG
theorem _root_.solution (P : PiecesF) : StCertGrid P := fun K => gridF_keeps K
end ClauseBound.Alg.CertGridG
