-- Prove2me | solution 1 for Exits.stCliqueOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:48:08.267716+00:00
-- url     : https://prove2.me/submissions/14759927-7d8c-4660-baee-5fa6a5b8830f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_SecLevel_EStar
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic.Ring
import Definitions.Def_Exits_Level
import Theorems.Thm_Exits_two_le_levelK
import Theorems.Thm_Eight_Level_levelE_nonneg
import Theorems.Thm_Groundwork_Prog_bruteE_correct
import Theorems.Thm_Groundwork_Prog_bruteE_keeps


set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Paper Eight Eight.SecNetworks Eight.ViaGrouping
namespace Exits
theorem _root_.solution : StCliqueOf := by
  intro h ℓ
  induction ℓ with
  | zero => exact ⟨bruteE_keeps _, bruteE_correct _⟩
  | succ ℓ ih => exact h (levelK ℓ) (Level.levelE ℓ) (CLIQUE ℓ) (two_le_levelK ℓ) (Level.levelE_nonneg ℓ) ih.1 ih.2
end Exits
