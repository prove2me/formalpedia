-- Prove2me | solution 1 for Exits.stByAlgorithmOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:33:00.539163+00:00
-- url     : https://prove2.me/submissions/4c5f6adc-705e-43c2-9b5a-539e546c4602

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_SecLevel_EStar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Exits_Decides
import Theorems.Thm_Paper_steps_to_time


set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping Suffices Enumerate
namespace Exits
theorem _root_.solution : StByAlgorithmOf := by
  intro h δ hδ
  obtain ⟨ℓ, τ, h1, h2⟩ := h (δ / 2) (by positivity)
  exact steps_to_time hδ _ h1 h2
end Exits
