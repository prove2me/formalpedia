-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.descFactorial_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:27:23.0494+00:00
-- url     : https://prove2.me/submissions/88c0f34b-033b-4810-bddd-d99b53ba0989

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_PaddedDescent_F_prodL_eq
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {n k : α → ℕ} (hn : PolyT n) (hk : Unary k) : PolyT fun x => (n x).descFactorial (k x) := by
  have h : PolyT fun x => (prodL (k x) fun i => ((n x - i : ℕ) : ℤ)).toNat :=
    PolyT.toNat (prodL_polyT (f := fun x i => ((n x - i : ℕ) : ℤ)) hk (PolyT.natCast (PolyT.sub (PolyT.comp hn PolyT.id'.fst) PolyT.id'.snd)))
  refine h.congr fun x => ?_
  rw [prodL_eq, ← Nat.cast_prod, Int.toNat_natCast, Nat.descFactorial_eq_prod_range]
end ClauseBound.ParityChecks.CertLib
