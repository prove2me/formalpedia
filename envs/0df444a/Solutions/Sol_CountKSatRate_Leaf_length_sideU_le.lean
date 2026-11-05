-- Prove2me | solution 1 for CountKSatRate.Leaf.length_sideU_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:40:41.692906+00:00
-- url     : https://prove2.me/submissions/43c26842-d79b-49b3-a4de-19bbc29c0b07

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSatRate_Leaf
import Theorems.Thm_Groundwork_DecodeK_IsKCNF_length_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Sat3_Is3CNF_length_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Leaf
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open PaddedDescent.F.Mark (occ nSat WfL)
namespace CountKSatRate.Leaf
theorem _root_.solution (X : PFml) : (sideU X).length ≤ X.length :=
  (List.dedup_sublist _).length_le.trans (List.length_filter_le _ _)
end CountKSatRate.Leaf
