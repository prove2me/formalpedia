-- Prove2me | solution 1 for Eight.stFact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:33.883206+00:00
-- url     : https://prove2.me/submissions/e55ea025-160a-4749-a10e-a7f0acac534f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Identity
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_PiecesAC
import Definitions.Def_Eight_SecCrossing_MulOut
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_Fact
import Definitions.Def_Eight_SecCrossing_Cert
import Definitions.Def_Eight_SecCrossing_LemPieces
import Theorems.Thm_Eight_A_eq_sum_subsets
import Theorems.Thm_Eight_stAMul
import Theorems.Thm_Eight_stChunk
import Theorems.Thm_Eight_stFact_of


set_option autoImplicit false
section
section
open Eight
open Groundwork
namespace Eight
theorem _root_.solution : StFact := stFact_of stChunk stAMul A_eq_sum_subsets
end Eight
