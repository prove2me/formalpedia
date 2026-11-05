-- Prove2me | solution 1 for ClausesOccur.boundInClausesFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:04:46.268824+00:00
-- url     : https://prove2.me/submissions/a9327fd6-36b7-4a9d-8e12-b2174d277244

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
import Theorems.Thm_ClausesOccur_boundInClausesIsHalf
import Theorems.Thm_GeneralPieces_Asymptotic_alpha_half


set_option autoImplicit false
section
section
open ClausesOccur
open Turing MainTheoremForms
namespace ClausesOccur
theorem _root_.solution : BoundInClausesFromStmt := by
  intro hB hC
  obtain ⟨c, P, A, val, h, -⟩ := hB
  obtain ⟨M, C, hfin, hM⟩ := hC _ c ⟨P, A, val, h⟩
  unfold AppRunningTime.alpha' at hM
  rw [GeneralPieces.Asymptotic.alpha_half] at hM
  exact ⟨M, C, hfin, (boundInClausesIsHalf M C).2 hM⟩
end ClausesOccur
