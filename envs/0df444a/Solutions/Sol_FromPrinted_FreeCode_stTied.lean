-- Prove2me | solution 1 for FromPrinted.FreeCode.stTied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:17:14.006536+00:00
-- url     : https://prove2.me/submissions/85038b95-7601-42a1-959d-409e7e717d09

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_ReaderCert
import Definitions.Def_FreeCode_Random
import Definitions.Def_FreeCode_Tied
import Definitions.Def_FreeCode_Main
import Definitions.Def_SplitSat_Walk
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Main
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Mathlib.Tactic
import Definitions.Def_FromPrinted_FreeCode
import Theorems.Thm_FreeCode_readFree_polyT
import Theorems.Thm_FreeCode_reads_readFree
import Theorems.Thm_FreeCode_tied_of_decidesW
import Theorems.Thm_FromPrinted_SplitSat_stCore3
import Theorems.Thm_SplitSat_endFrom
import Theorems.Thm_SplitSat_eth_and_seth_false
import Theorems.Thm_SplitSat_reduceCore_polyTimeSteps
import Theorems.Thm_SplitSat_stCore3
import Theorems.Thm_SplitSat_stReduceCore
import Theorems.Thm_SplitSat_stSATsplit
import Theorems.Thm_SplitSat_stSparsifyK
import Theorems.Thm_SplitSat_stTiedTM
import Theorems.Thm_SplitSat_stTiedThreeTM
import Theorems.Thm_WidthK_Prog_certStep


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper FreeCode SatFree
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement stSATsplit stTiedTM stTiedThreeTM endFrom eth_and_seth_false
open FromPrinted.SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.FreeCode
namespace FromPrinted.FreeCode
theorem _root_.solution : StTied := fun k hk δ hδ => by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨τ, Dd, B, Sk, hsp⟩ := stSparsifyK k hk (δ / 2 / 3) (by positivity)
  have hk3 : (0 : ℝ) ≤ (k : ℝ) - 3 := by
    have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hpos : (0 : ℝ) < 1 + ((k : ℝ) - 3) * B := by
    have := mul_nonneg hk3 (Nat.cast_nonneg (α := ℝ) B)
    linarith
  have h0 : 0 < δ / 2 / 3 / (1 + ((k : ℝ) - 3) * B) := div_pos (by positivity) hpos
  obtain ⟨ℓ₃, τ₃, hp, c₃, hD⟩ := FromPrinted.SplitSat.stCore3 _ h0
  obtain ⟨c₀, hR⟩ := stReduceCore k hk (δ / 2) hδ2 τ Dd B Sk hsp (core3 ℓ₃ τ₃) _ c₃ h0.le (le_of_eq (div_mul_cancel₀ _ hpos.ne')) hD
  obtain ⟨M, c, q, h⟩ := tied_of_decidesW hδ (reduceCore_polyTimeSteps (certStep (thetaU τ) k) hp) hR
  exact ⟨readFree, τ, ℓ₃, τ₃, M, c, q, readFree_polyT, reads_readFree, h⟩
end FromPrinted.FreeCode
