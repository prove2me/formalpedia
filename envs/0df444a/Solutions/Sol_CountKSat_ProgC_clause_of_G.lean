-- Prove2me | solution 1 for CountKSat.ProgC.clause_of_G
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:01:38.142073+00:00
-- url     : https://prove2.me/submissions/6b201723-a351-455a-b2b9-f5607b508c1c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSat_ProgC
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_ProgMain_mem_toFin
import Theorems.Thm_WidthK_Refine_mem_toFin
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
open CountKSat.ProgC
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}
namespace CountKSat.ProgC
theorem _root_.solution (hI : Iface θ k D T q leafB Ok Node) {n : ℕ} {ψ : PFml} (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n)
    {s : PFml} {p t : ℕ} (hG : ProgMain.G Node ψ s p t) : ∀ C ∈ s, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
  intro C hC
  obtain ⟨X₀, hX₀, hsub⟩ := hI.clause _ _ _ _ hG.2 _ (ProgMain.mem_toFin.2 ⟨C, hC, rfl⟩)
  obtain ⟨C₀, hC₀, rfl⟩ := ProgMain.mem_toFin.1 hX₀
  refine ⟨?_, fun l hl => (hψ C₀ hC₀).2 l (List.mem_toFinset.1 (hsub (List.mem_toFinset.2 hl)))⟩
  rw [← List.toFinset_card_of_nodup (hG.1.1 C hC)]
  exact (card_le_card hsub).trans ((List.toFinset_card_le C₀).trans (hψ C₀ hC₀).1)
end CountKSat.ProgC
