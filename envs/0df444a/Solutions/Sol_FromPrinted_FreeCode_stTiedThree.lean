-- Prove2me | solution 1 for FromPrinted.FreeCode.stTiedThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:19:23.610196+00:00
-- url     : https://prove2.me/submissions/8242d4ea-b995-41db-bf7b-b1eaebacb070

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
import Theorems.Thm_SplitSat_stCore3
import Theorems.Thm_SplitSat_stSATsplit
import Theorems.Thm_SplitSat_stTiedTM
import Theorems.Thm_SplitSat_stTiedThreeTM


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper FreeCode SatFree
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement stSATsplit stTiedTM stTiedThreeTM endFrom eth_and_seth_false
open FromPrinted.SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.FreeCode
namespace FromPrinted.FreeCode
theorem _root_.solution : StTiedThree := fun δ hδ => by
  obtain ⟨ℓ, τ, hp, c₀, hD⟩ := FromPrinted.SplitSat.stCore3 (δ / 2) (by positivity)
  obtain ⟨M, c, q, h⟩ := tied_of_decidesW hδ hp hD
  exact ⟨readFree, ℓ, τ, M, c, q, readFree_polyT, reads_readFree, h⟩
end FromPrinted.FreeCode
