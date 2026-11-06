-- Prove2me | solution 1 for FreeCode.stTiedThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:51:23.205416+00:00
-- url     : https://prove2.me/submissions/099da8c6-1ee5-4467-aa24-aa8fc9ebd1b1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_ReaderCert
import Definitions.Def_FreeCode_Behind
import Definitions.Def_SplitSat_Walk
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SplitSat_Main
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
import Definitions.Def_FreeCode_Tied
import Theorems.Thm_FreeCode_tied_of_decidesW
import Theorems.Thm_FreeCode_readFree_polyT
import Theorems.Thm_FreeCode_reads_readFree
import Theorems.Thm_SplitSat_stCore3


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper SplitSat
namespace FreeCode
theorem _root_.solution : StTiedThree := fun δ hδ => by
  obtain ⟨ℓ, τ, hp, c₀, hD⟩ := stCore3 (δ / 2) (by positivity)
  obtain ⟨M, c, q, h⟩ := tied_of_decidesW hδ hp hD
  exact ⟨readFree, ℓ, τ, M, c, q, readFree_polyT, reads_readFree, h⟩
end FreeCode
