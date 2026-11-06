-- Prove2me | solution 1 for Eight.ViaGrouping.Cost.serves_Bp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:37:28.958879+00:00
-- url     : https://prove2.me/submissions/aaee5980-0900-42b9-95c1-37ee4ef0c447

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
import Theorems.Thm_Eight_ViaGrouping_Cost_le_Bp
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Cost
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g : ℕ} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping.Cost
theorem _root_.solution {D : Type} {R : Stepped (D × IQ) ℤ} {d : D} {K : ℕ} {L t S' : ℕ} {W : Paper.Tables K} (g P B : ℕ)
    (h : ServesInst R d L (P * (2 * g / K) + g ^ 2 * B) t S' W) : ServesInst R d L (Bp K g P B) t S' W := fun v θ hθ hv =>
  ⟨(h v θ hθ hv).1, (h v θ hθ hv).2.trans (pow_le_pow_right₀ (by norm_num) (le_Bp K g P B))⟩
end Eight.ViaGrouping.Cost
