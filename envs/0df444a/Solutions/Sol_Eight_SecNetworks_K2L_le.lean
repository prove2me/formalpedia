-- Prove2me | solution 1 for Eight.SecNetworks.K2L_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:25:13.970345+00:00
-- url     : https://prove2.me/submissions/472764e5-13bf-4e0e-9ed2-391b83bbd5d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Theorems.Thm_Paper_groupedLength_le


set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset Stepped
namespace Eight.SecNetworks
theorem _root_.solution (K g U P : ℕ) : K ^ 3 * Paper.groupedLength K g U P ≤ K ^ 3 + K * U + g * P := Paper.groupedLength_le K g U P
end Eight.SecNetworks
