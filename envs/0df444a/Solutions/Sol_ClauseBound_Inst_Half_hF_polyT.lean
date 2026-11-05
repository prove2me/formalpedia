-- Prove2me | solution 1 for ClauseBound.Inst.Half.hF_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:29:38.964207+00:00
-- url     : https://prove2.me/submissions/9e86c352-79ad-4d5a-b3a8-0644f4dd6e05

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfPart
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Theorems.Thm_ClauseBound_Inst_Half_pTab_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half
theorem _root_.solution (c₀ : ℕ) {lam : α → ℕ} (hl : Unary lam) : PolyT fun x => hF c₀ (lam x) := by
  have hN : Unary fun x => c₀ * lam x ^ 2 := (Unary.const c₀).mul (unary_pow_const hl 2)
  have hT : PolyT fun x => pTab (c₀ * lam x ^ 2) := pTab_polyT hN
  have hpow : PolyT fun x => 2 ^ lam x := pow_polyT (PolyT.const 2) hl
  have hr : PolyT fun x => List.range (c₀ * lam x ^ 2 + 1) := PolyT.range (hN.add (Unary.const 1))
  have hpred : PolyT fun q : α × ℕ => decide (2 ≤ q.2) && decide (2 ^ lam q.1 ≤ (pTab (c₀ * lam q.1 ^ 2)).getD q.2 0) := by
    have h1 : PolyT fun q : α × ℕ => pTab (c₀ * lam q.1 ^ 2) := PolyT.comp (f := fun x => pTab (c₀ * lam x ^ 2)) hT PolyT.id'.fst
    have h2 : PolyT fun q : α × ℕ => 2 ^ lam q.1 := PolyT.comp (f := fun x => 2 ^ lam x) hpow PolyT.id'.fst
    exact PolyT.and' (PolyT.decide_le (PolyT.const 2) PolyT.id'.snd) (PolyT.decide_le h2 (PolyT.getD h1 PolyT.id'.snd (PolyT.const 0)))
  unfold hF
  exact PolyT.optionGetD (PolyT.find? hpred hr) (PolyT.const 2)
end ClauseBound.Inst.Half
