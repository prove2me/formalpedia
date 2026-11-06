-- Prove2me | solution 1 for Exits.stKeepsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:17:44.760001+00:00
-- url     : https://prove2.me/submissions/45eb7e13-4845-4f08-8404-aad63c86cdd3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Main
import Definitions.Def_Eight_ViaGrouping_Keeps
import Definitions.Def_ToTuring_Poly_Range
import Mathlib.Tactic.GCongr
import Definitions.Def_Exits_Grouping
import Theorems.Thm_Exits_search_isPolyT
import Theorems.Thm_Eight_SecNetworks_keeps_toPaperNetwork
import Theorems.Thm_Eight_ViaGrouping_lamP_unary
import Theorems.Thm_Groundwork_Prog_NetE_zeroOf_polyT
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem


set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset Paper Eight Eight.SecNetworks Eight.ViaGrouping Eight.ViaGrouping.Cost
namespace Exits
theorem _root_.solution : StKeepsOf := by
  intro hF K g E hE C _ _ _ Np hN
  have hk := keeps_toPaperNetwork hN.keeps
  obtain ⟨hm⟩ := hN.keeps.mem
  obtain ⟨hW⟩ := hN.keeps.W
  obtain ⟨hΨ⟩ := hN.keeps.Ψ
  obtain ⟨hf⟩ := hN.keeps.f
  obtain ⟨hE'⟩ := hE (C × ℕ) (lamP K g Np) (tableM K g Np) (lamP_unary K g hN) ⟨tableM_isPolyT K g hk⟩
  obtain ⟨hs⟩ := search_isPolyT hF K g hN
  exact ⟨IsPolyT.optBind zeroOf_polyT⟩
end Exits
