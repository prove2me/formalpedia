-- Prove2me | solution 1 for FromPrinted.SplitSat.stSATsplit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:16:30.147886+00:00
-- url     : https://prove2.me/submissions/eed22171-6396-4a79-b07e-c88f606152da

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
import Theorems.Thm_FromPrinted_SplitSat_stCore3
import Theorems.Thm_SplitSat_exists_parameters
import Theorems.Thm_SplitSat_stCore3


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.SplitSat
namespace FromPrinted.SplitSat
theorem _root_.solution : StSATsplit := fun k hk δ hδ => by
  obtain ⟨τ, δ₃, h0, h⟩ := exists_parameters k hk δ hδ
  obtain ⟨ℓ₃, τ₃, hp, c, hD⟩ := stCore3 δ₃ h0
  exact ⟨τ, ℓ₃, τ₃, h (core3 ℓ₃ τ₃) c hp hD⟩
end FromPrinted.SplitSat
