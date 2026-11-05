-- Prove2me | solution 1 for ClauseBound.ParityChecks.Count.toNat_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:10:43.58237+00:00
-- url     : https://prove2.me/submissions/8315b234-e1e3-43b7-aa5b-aec2117cf191

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_ClauseBound_ParityChecks_Count
import Theorems.Thm_ClauseBound_ParityChecks_div_congr
import Theorems.Thm_ClauseBound_ParityChecks_emod_eq
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Count
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks
namespace ClauseBound.ParityChecks.Count
theorem _root_.solution {a : ℤ} {N n r β : ℕ} (h : a ≡ 2 ^ r * (N : ℤ) [ZMOD 2 ^ (β - 1 + r + 1)]) (hβ : n + 2 ≤ β) (hN : N ≤ 2 ^ n) :
    ((a / 2 ^ r) % 2 ^ (n + 1)).toNat = N := by
  have e : β - 1 + r + 1 = β + r := by omega
  rw [e] at h
  have h1 := (div_congr h).of_dvd (pow_dvd_pow (2 : ℤ) (by omega : n + 1 ≤ β))
  rw [emod_eq (Int.natCast_nonneg N) (by exact_mod_cast hN) h1, Int.toNat_natCast]
end ClauseBound.ParityChecks.Count
