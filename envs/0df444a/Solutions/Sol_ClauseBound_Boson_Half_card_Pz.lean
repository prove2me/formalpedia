-- Prove2me | solution 1 for ClauseBound.Boson.Half.card_Pz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:52:12.857762+00:00
-- url     : https://prove2.me/submissions/bd2ce337-a622-4c83-906d-06a19d35894f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_HalfSum
import Definitions.Def_ClauseBound_Rec_Number
import Definitions.Def_ClauseBound_Boson_Half
import Theorems.Thm_ClauseBound_Boson_HalfSum_coe_lst
import Theorems.Thm_ClauseBound_Boson_HalfSum_pos_lst
import Theorems.Thm_ClauseBound_Boson_HalfSum_sum_lst
import Theorems.Thm_ClauseBound_Boson_HalfSum_zero_notMem_parts
import Theorems.Thm_ClauseBound_Boson_card_P


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Half
open HalfSum (coe_lst sum_lst pos_lst zero_notMem_parts)
namespace ClauseBound.Boson.Half
theorem _root_.solution (m : ℤ) : #(Pz m) = ClauseBound.Part.pz m := by
  unfold Pz ClauseBound.Part.pz
  split_ifs
  · exact card_P _
  · exact card_empty
end ClauseBound.Boson.Half
