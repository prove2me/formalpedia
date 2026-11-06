-- Prove2me | solution 1 for ClausesOccur.countsFromPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:38:07.971264+00:00
-- url     : https://prove2.me/submissions/e2056f47-de62-42f0-90bd-3d77fe1536af

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_OccurM_Arith
import Definitions.Def_OccurM_Top
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_GeneralPieces_Num_PartD
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_OccurM_Main
import Theorems.Thm_OccurM_countsFromPiecesTied
import Theorems.Thm_OccurM_untie

set_option autoImplicit false
section
section
open ClausesOccur
open Turing MainTheoremForms
namespace ClausesOccur
theorem _root_.solution : CountsFromPieces := (OccurM.untie.1 OccurM.countsFromPiecesTied).1
end ClausesOccur
