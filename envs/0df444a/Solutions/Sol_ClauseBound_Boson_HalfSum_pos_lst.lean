-- Prove2me | solution 1 for ClauseBound.Boson.HalfSum.pos_lst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:19:32.47793+00:00
-- url     : https://prove2.me/submissions/762e7b5a-63d4-4e21-934e-dd32706e368f

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
theorem _root_.solution {h : ℕ} (q : Nat.Partition h) : Pos (lst q) := fun _ hn => q.parts_pos (Multiset.mem_toList.1 hn)
end ClauseBound.Boson.HalfSum
