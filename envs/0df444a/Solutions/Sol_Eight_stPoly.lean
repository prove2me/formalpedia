-- Prove2me | solution 1 for Eight.stPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:02.086347+00:00
-- url     : https://prove2.me/submissions/cc13949f-7f9d-4a6b-b1fa-da469fa2d410

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_MulOut
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_Eight_SecCrossing_Cert
import Theorems.Thm_Eight_SecCrossing_Cert_aMul_polyT
import Theorems.Thm_Eight_SecCrossing_Cert_fTop_polyT
import Theorems.Thm_Eight_SecCrossing_Cert_fBot_polyT

set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F ClauseBound.Alg SingleBitPieces.SecCrossing_PolyA
open SecCrossing_Cert
namespace Eight
theorem _root_.solution : StPoly := ⟨aMul_polyT, fTop_polyT, fBot_polyT⟩
end Eight
