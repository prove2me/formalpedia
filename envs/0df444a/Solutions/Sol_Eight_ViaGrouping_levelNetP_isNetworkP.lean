-- Prove2me | solution 1 for Eight.ViaGrouping.levelNetP_isNetworkP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:15:13.609601+00:00
-- url     : https://prove2.me/submissions/ac484ffc-aac9-45c7-8c71-be7708217331

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Level
import Definitions.Def_Eight_ViaGrouping_LevelCert
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Theorems.Thm_Eight_Level_stPresents_of
import Theorems.Thm_Eight_ViaGrouping_levelNetP_isNetworkP_printed_of
import Theorems.Thm_Eight_ViaGrouping_stPsiOK
import Theorems.Thm_Eight_stPieces


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (g : ℕ) (hg : 1 ≤ g) : ∃ a : ℕ, ∀ (tr : Bool) (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
    (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ), 1 ≤ lam c → 1 ≤ t → y < (tOf (lam c) + 1) ^ nRect g → ServesInst R c (lam c) B t S Rm →
    IsNetworkP (levelProcs g tr (gridPsi g tr) lam R) (c, y) (levelNetP g tr (lam c) y Rm) (g ^ 3 * lam c) (g * B + g ^ 2 * lam c + 1)
      (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a + 2) :=
  let ⟨a, ha⟩ := levelNetP_isNetworkP_printed_of (stPresents_of stPieces) g hg
  ⟨a, fun tr => ha tr _ (stPsiOK g tr)⟩
end Eight.ViaGrouping
