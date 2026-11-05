-- Prove2me | solution 1 for CountKSat.ProgC.pick_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:17:12.574779+00:00
-- url     : https://prove2.me/submissions/6a4fad78-6db4-4453-8b42-60b42f85472a

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
import Theorems.Thm_CountKSat_ProgC_clause_of_G
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_ProgMain_mem_toFin
import Theorems.Thm_WidthK_Refine_mem_toFin
import Theorems.Thm_WidthK_SetAlg_exists_over
import Theorems.Thm_WidthK_SetAlg_mem_over
import Theorems.Thm_WidthK_Step_exists_over
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
theorem _root_.solution (hθ : ∀ i, 1 ≤ θ i) (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {n : ℕ} {ψ : PFml}
    (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) {s : PFml} {p t : ℕ} (hG : ProgMain.G Node ψ s p t) {H : PCl} {P : PFml}
    (hp : pickK θ k s = some (H, P)) :
    H.length ≤ k ∧ ∀ l ∈ H, l.1 < n := by
  obtain ⟨j, hrule, -, -, hH⟩ := hR.some s H P hG.1 hp
  refine ⟨?_, ?_⟩
  · rw [← List.toFinset_card_of_nodup hH]
    exact (hrule.heart.2.1.le).trans hrule.le
  · intro l hl
    obtain ⟨X, hX⟩ := SetAlg.exists_over hθ hrule.heart
    obtain ⟨hXF, -, hsub⟩ := SetAlg.mem_over.1 hX
    obtain ⟨C, hC, rfl⟩ := ProgMain.mem_toFin.1 hXF
    exact (clause_of_G hI hψ hG C hC).2 l (List.mem_toFinset.1 (hsub (List.mem_toFinset.2 hl)))
end CountKSat.ProgC
