-- Prove2me | solution 1 for ClauseBound.Boson.HalfSum.sum_lst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:19:07.359602+00:00
-- url     : https://prove2.me/submissions/1232fd19-0d43-4117-9ddc-61d24516bbcb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_HalfSum

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.HalfSum
open Finset
namespace ClauseBound.Boson.HalfSum
theorem _root_.solution {h : ℕ} (q : Nat.Partition h) : (lst q).sum = h := by
  rw [lst, Multiset.sum_toList, q.parts_sum]
end ClauseBound.Boson.HalfSum
