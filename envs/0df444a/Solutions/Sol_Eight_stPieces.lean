-- Prove2me | solution 1 for Eight.stPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:11.437126+00:00
-- url     : https://prove2.me/submissions/c3916233-67b8-4da9-aa88-c5ca58eda810

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_Eight_Level_Pieces
import Definitions.Def_Eight_Level_Presents
import Definitions.Def_Eight_Level_Cert
import Definitions.Def_Eight_Level_Min
import Definitions.Def_Eight_Level_Arith
import Definitions.Def_StepMachines_Prog_GridLoop
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_Eight_Level_SecPseudocode
import Definitions.Def_Eight_SecLevel_EStar
import Definitions.Def_Eight_Level_End
import Theorems.Thm_Eight_Level_stPieces_of_lemPieces
import Theorems.Thm_Eight_lemPieces
import Theorems.Thm_Eight_stFact


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog Paper
namespace Eight
theorem _root_.solution : Level.StPieces := Level.stPieces_of_lemPieces lemPieces stFact
end Eight
