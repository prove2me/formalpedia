-- Prove2me | solution 1 for Eight.ViaGrouping.stEngine_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:28:12.727597+00:00
-- url     : https://prove2.me/submissions/a152fe6e-3ae8-47b5-9188-5ec87b01cafa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_Graph
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_DomTree
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorGraph

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat GraphProblems Finset Turing
variable {En : ℕ → ℕ → ℕ → StepMachine (List Unit × Fml) (List Bool)}
namespace Eight.ViaGrouping
theorem _root_.solution (h : EngineCounts En) : StEngine := fun k hk δ hδ =>
  let ⟨ℓ, τ, hp, hc⟩ := h k hk δ hδ
  ⟨En k ℓ τ, hp, hc⟩
end Eight.ViaGrouping
