-- Prove2me | solution 1 for ClauseBound.Inst.Half.HalfTabKF.kfStep_entry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:38:26.694138+00:00
-- url     : https://prove2.me/submissions/202e4e1d-9bcc-4717-b2cf-59ba41766d63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_KF
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Theorems.Thm_ClauseBound_Inst_Half_HalfTabKF_sum_Icc_one
import Theorems.Thm_ClauseBound_Boson_KF_cons
import Theorems.Thm_ClauseBound_Inst_Half_nopE_eq
import Theorems.Thm_ClauseBound_Inst_Rec_chooseZ_eq
import Theorems.Thm_ClauseBound_Inst_Rec_sgnZ_eq
import Theorems.Thm_ClauseBound_Inst_Rec_sumR_eq
import Theorems.Thm_ClauseBound_Rec_ite_even_natCast
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open ClauseBound.Inst.Half.HalfTabKF
namespace ClauseBound.Inst.Half.HalfTabKF
theorem _root_.solution {W h n w : ℕ} {flat : List (List ℕ)} {S : List (List ℤ)} {μ : List ℕ} (hf : FlatOK W flat) (hn : n ≤ W)
    (hS : ∀ w ≤ h, Rep flat (S.getD w []) (KF μ w)) (hw : w ≤ h) {π σ : List ℕ} (hπ : π ∈ flat) (hσ : σ ∈ flat) :
    (sumR (min n W) fun j =>
      if j + 1 ≤ w then sgnZ ((n - 1 : ℕ) : ℤ) * chooseZ (n : ℤ) (j + 1) * nopE W (j + 1) flat (S.getD (w - (j + 1)) []) π σ else 0) =
      KF (n :: μ) w ((π.sum : ℤ) - σ.sum) π σ := by
  rw [KF_cons, sum_Icc_one, sumR_eq, min_eq_left hn]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j + 1 ≤ W := (Nat.succ_le_of_lt (mem_range.1 hj)).trans hn
  refine if_congr Iff.rfl ?_ rfl
  rw [sgnZ_eq, ClauseBound.Rec.ite_even_natCast, chooseZ_eq, Ring.choose_natCast, nopE_eq hf hj' (hS _ ((Nat.sub_le _ _).trans hw)) hπ hσ]
end ClauseBound.Inst.Half.HalfTabKF
