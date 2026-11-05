-- Prove2me | solution 1 for Eight.SecCrossing_Cert.psi_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:18:53.902805+00:00
-- url     : https://prove2.me/submissions/63130f99-5e42-4043-9d39-3b3fcfc28f1b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_MulOut
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_Eight_SecCrossing_Cert
import Theorems.Thm_P2M_Groundwork_PolyT_table__55b65ec90c5c


set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F ClauseBound.Alg SingleBitPieces.SecCrossing_PolyA
open Eight.SecCrossing_Cert
variable {α : Type} [Enc α]
namespace Eight.SecCrossing_Cert
theorem _root_.solution {k p q : α → Block} (hk : PolyT k) (hp : PolyT p) (hq : PolyT q) : PolyT fun x => psi (k x) (p x) (q x) :=
  PolyT.table₃ psi hk hp hq
end Eight.SecCrossing_Cert
