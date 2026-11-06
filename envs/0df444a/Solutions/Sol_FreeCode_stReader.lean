-- Prove2me | solution 1 for FreeCode.stReader
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:36:52.621681+00:00
-- url     : https://prove2.me/submissions/6d3b5593-ce70-4f7c-8e13-0b73d34f3913

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Reader
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_FreeCode_ReaderCert
import Theorems.Thm_FreeCode_readFree_polyT
import Theorems.Thm_FreeCode_reads_readFree


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
namespace FreeCode
theorem _root_.solution : StReader := ⟨readFree, readFree_polyT, reads_readFree⟩
end FreeCode
