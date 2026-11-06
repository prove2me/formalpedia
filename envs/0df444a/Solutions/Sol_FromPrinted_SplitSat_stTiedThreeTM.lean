-- Prove2me | solution 1 for FromPrinted.SplitSat.stTiedThreeTM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:10:59.318183+00:00
-- url     : https://prove2.me/submissions/17cbb942-8324-4150-aa54-012dd9109421

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_Printed_End
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SplitSat_Main
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
import Definitions.Def_FromPrinted_SplitSat
import Theorems.Thm_Exits_stDecides
import Theorems.Thm_Printed_stDecides
import Theorems.Thm_SplitSat_decidesTM_of_simulates
import Theorems.Thm_SplitSat_decides_mono
import Theorems.Thm_SplitSat_exists_simulates


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.SplitSat
namespace FromPrinted.SplitSat
theorem _root_.solution : StTiedThreeTM := fun δ hδ => by
  obtain ⟨ℓ, τ, hp, c, hd⟩ := Printed.stDecides (δ / 2) (by positivity)
  have hd' : Decides (Printed.SAT ℓ τ) 3 (δ / 2) c := hd
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp
  obtain ⟨C, hcC, hTM⟩ := decidesTM_of_simulates hδ hs hd'
  exact ⟨ℓ, τ, M, C, q, hfin, hp, decides_mono (by linarith) hcC hd', hs, hTM⟩
end FromPrinted.SplitSat
