-- Prove2me | solution 1 for Exits.stDecidesOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:32:58.08531+00:00
-- url     : https://prove2.me/submissions/10aefe27-0eba-4c5e-a35c-f86aaebca08c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_SecLevel_EStar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Exits_Decides
import Theorems.Thm_Eight_decidesInSteps_mono


set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping Suffices Enumerate
namespace Exits
theorem _root_.solution : StDecidesOf := by
  intro hA hEn δ hδ
  have hδ₀ : 0 < min δ 1 := lt_min hδ one_pos
  obtain ⟨M, τ, hM, hE⟩ := hEn (min δ 1 / 3) (by positivity)
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hδ' : 0 < min δ 1 / (3 * (M : ℝ)) := by positivity
  obtain ⟨h1, h2⟩ := hA (min δ 1) M τ hδ' hδ₀ (min_le_right _ _) hM hE
  exact ⟨Level.firstLevel hδ', τ, h1, decidesInSteps_mono h2 (min_le_left _ _)⟩
end Exits
