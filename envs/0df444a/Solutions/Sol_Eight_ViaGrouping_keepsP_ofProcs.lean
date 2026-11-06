-- Prove2me | solution 1 for Eight.ViaGrouping.keepsP_ofProcs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:44:01.440341+00:00
-- url     : https://prove2.me/submissions/629d44c8-d849-415b-a7f6-cdc9bcfaa274

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge
import Theorems.Thm_Eight_ViaGrouping_keeps_ofProcs

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution {C : Type} [HasSize C] [Enc C] [Carried C] {Np : PNet C} {Pf : C → ℕ} {Q : Stepped (C × PsiQ) ℤ} (h : Np.Keeps) (hP : Unary Pf) (hQ : Nonempty (IsPolyT Q)) :
    KeepsP (ofProcs Np Pf Q) := ⟨keeps_ofProcs Pf h hQ, hP⟩
end Eight.ViaGrouping
