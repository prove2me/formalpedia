-- Prove2me | solution 1 for Eight.lemPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:25.747477+00:00
-- url     : https://prove2.me/submissions/0f294382-bdff-4331-89de-286d11d91613

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
import Theorems.Thm_Eight_stFact
import Theorems.Thm_Eight_a_abs
import Theorems.Thm_Eight_a_sum
import Theorems.Thm_Eight_c_col
import Theorems.Thm_Eight_c_row
import Theorems.Thm_Eight_c_sum
import Theorems.Thm_Eight_crow_add_ccol_le
import Theorems.Thm_Eight_lemPieces_b_col
import Theorems.Thm_Eight_lemPieces_b_row
import Theorems.Thm_Eight_signs


set_option autoImplicit false
section
section
open Eight
open Groundwork
namespace Eight
theorem _root_.solution : LemPieces :=
  ⟨a_sum signs, a_abs, lemPieces_b_row stFact, lemPieces_b_col stFact, c_row, c_col, fun _ _ _ hi => crow_add_ccol_le hi, c_sum⟩
end Eight
