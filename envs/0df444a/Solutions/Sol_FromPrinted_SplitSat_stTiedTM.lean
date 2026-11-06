-- Prove2me | solution 1 for FromPrinted.SplitSat.stTiedTM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:22:35.081108+00:00
-- url     : https://prove2.me/submissions/ecb01774-0af5-4f62-8e34-616c0481e76a

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
import Theorems.Thm_FromPrinted_SplitSat_stSATsplit
import Theorems.Thm_SplitSat_decidesTM_of_simulates
import Theorems.Thm_SplitSat_decides_mono
import Theorems.Thm_SplitSat_exists_simulates
import Theorems.Thm_SplitSat_stSATsplit


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.SplitSat
namespace FromPrinted.SplitSat
theorem _root_.solution : StTiedTM := fun k hk δ hδ => by
  obtain ⟨τ, ℓ₃, τ₃, hp, c, hd⟩ := stSATsplit k hk (δ / 2) (by positivity)
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp
  obtain ⟨C, hcC, hTM⟩ := decidesTM_of_simulates hδ hs hd
  exact ⟨τ, ℓ₃, τ₃, M, C, q, hfin, hp, decides_mono (by linarith) hcC hd, hs, hTM⟩
end FromPrinted.SplitSat
