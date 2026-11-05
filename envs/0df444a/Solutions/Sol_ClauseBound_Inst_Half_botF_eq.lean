-- Prove2me | solution 1 for ClauseBound.Inst.Half.botF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:55:18.884768+00:00
-- url     : https://prove2.me/submissions/38e50e0e-b276-4024-b9a1-8eb1e96e3844

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Theorems.Thm_ClauseBound_Inst_Half_zzF_eq
import Theorems.Thm_ClauseBound_Boson_op_grade
import Theorems.Thm_ClauseBound_Inst_Half_tabOp_rep
import Theorems.Thm_ClauseBound_Inst_Rec_factN_eq
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
namespace ClauseBound.Inst.Half
theorem _root_.solution {pad : U} {W : ℕ} {flat : List (List ℕ)} {μ : List ℕ} (hW : 1 ≤ W) (hf : FlatOK W flat) (hμ : ∀ n ∈ μ, n ≤ W)
    (hp : padOp W flat.length μ.length ≤ pad.length) (h : ℕ) (r : ℤ) {π σ : List ℕ} (hπ : π ∈ flat) (hσ : σ ∈ flat) :
    botF pad W flat h μ r π σ = ClauseBound.Boson.botK μ h r ↑π ↑σ := by
  unfold botF botK
  by_cases hr : r = (π.sum : ℤ) - σ.sum
  · rw [if_pos hr, factN_eq, zzF_eq, tabOp_rep hW hf hμ hp π hπ σ hσ, hr]
  · rw [if_neg hr]
    have h0 : op μ r (π : Multiset ℕ) (σ : Multiset ℕ) = 0 := by
      by_contra hne
      have hg := op_grade hne
      rw [Multiset.sum_coe, Multiset.sum_coe] at hg
      exact hr (by omega)
    rw [h0, mul_zero]
end ClauseBound.Inst.Half
