-- Prove2me | solution 1 for ClauseBound.Inst.Half.tabKF_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:48:15.194432+00:00
-- url     : https://prove2.me/submissions/8e5e41be-556c-4360-b499-098eb528e32f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_KF
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Theorems.Thm_ClauseBound_Inst_Half_HalfTabKF_padKF_mono
import Theorems.Thm_ClauseBound_Inst_Half_HalfTabKF_rep_cap
import Theorems.Thm_ClauseBound_Inst_Half_HalfTabKF_kfInit_eq
import Theorems.Thm_ClauseBound_Inst_Half_HalfTabKF_kfStep_entry
import Theorems.Thm_ClauseBound_Boson_KF_nil
import Theorems.Thm_ClauseBound_Boson_abs_KF_le
import Theorems.Thm_ClauseBound_Inst_Half_lookT_tab
import Theorems.Thm_ClauseBound_Inst_Half_oneT_rep
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open HalfTabKF
namespace ClauseBound.Inst.Half
theorem _root_.solution {pad : U} {W h : ℕ} {flat : List (List ℕ)} {μ : List ℕ} (hW : 1 ≤ W) (hf : FlatOK W flat) (hμ : ∀ n ∈ μ, n ≤ W)
    (hp : padKF W flat.length h μ.sum μ.length ≤ pad.length) : ∀ w ≤ h, Rep flat ((tabKF pad W flat h μ).getD w []) (ClauseBound.Boson.KF μ w) := by
  induction μ with
  | nil =>
    have e : tabKF pad W flat h [] = cap pad [] (kfInit h flat) := rfl
    rw [e, kfInit_eq]
    refine rep_cap (B := 0 + (4 * W + 1) * 0) hf (fun w _ π hπ σ hσ => ?_) (fun w r π σ h1 h2 => abs_KF_le hW [] hμ w r h1 h2) hp
    rw [KF_nil]
    refine if_congr Iff.rfl ?_ rfl
    have h0 := oneT_rep hf π hπ σ hσ
    rwa [oneT, lookT_tab _ hπ hσ] at h0
  | cons n μ ih =>
    have e : tabKF pad W flat h (n :: μ) = cap pad [] (kfStep W h n flat (tabKF pad W flat h μ)) := by
      unfold tabKF
      rw [List.reverse_cons, List.foldl_append]
      rfl
    have hS := ih (fun m hm => hμ m (List.mem_cons_of_mem _ hm))
      ((padKF_mono W flat.length h (by rw [List.sum_cons]; omega) (by rw [List.length_cons]; omega)).trans hp)
    rw [e]
    exact rep_cap hf (fun w hw π hπ σ hσ => kfStep_entry hf (hμ n List.mem_cons_self) hS hw hπ hσ)
      (fun w r π σ h1 h2 => abs_KF_le hW (n :: μ) hμ w r h1 h2) hp
end ClauseBound.Inst.Half
