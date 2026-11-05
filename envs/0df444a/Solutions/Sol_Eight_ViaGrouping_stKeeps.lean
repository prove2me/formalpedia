-- Prove2me | solution 1 for Eight.ViaGrouping.stKeeps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:20:13.07159+00:00
-- url     : https://prove2.me/submissions/7710ec37-b97a-4735-bae7-465df2890a65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_Eight_ViaGrouping_Keeps
import Theorems.Thm_Eight_ViaGrouping_lamP_unary
import Theorems.Thm_Eight_SecNetworks_keeps_toPaperNetwork
import Theorems.Thm_Groundwork_Prog_NetE_zeroOf_polyT
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] [Enc C] [Carried C] (K g : ℕ) {Np : Procs C}
namespace Eight.ViaGrouping
theorem _root_.solution : StKeeps := by
  intro K g E hE C _ _ _ Np hN
  have hk := keeps_toPaperNetwork hN.keeps
  obtain ⟨hm⟩ := hN.keeps.mem
  obtain ⟨hW⟩ := hN.keeps.W
  obtain ⟨hΨ⟩ := hN.keeps.Ψ
  obtain ⟨hf⟩ := hN.keeps.f
  obtain ⟨hE'⟩ := hE (C × ℕ) (lamP K g Np) (tableM K g Np) (lamP_unary K g hN) ⟨tableM_isPolyT K g hk⟩
  have := searchP_isPolyT K g hN
  exact ⟨IsPolyT.optBind zeroOf_polyT⟩
end Eight.ViaGrouping
