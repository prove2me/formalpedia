-- Prove2me | solution 1 for CountKSat.stDecU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:46:49.688779+00:00
-- url     : https://prove2.me/submissions/1f87c65f-160e-4673-bdac-69da250e7141

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_WidthK_Poly_Decode
import Definitions.Def_CountKSat_InOut
import Theorems.Thm_Groundwork_DecodeK_decK_enc
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_takeWhile
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.takeWhile



set_option autoImplicit false
section
open CountKSat
open Groundwork Groundwork.Prog Groundwork.Decode Groundwork.DecodeK
open SatK (enc numSat)
namespace CountKSat
theorem _root_.solution : StDecU := fun k n φ hk hφ => by
  have h := decK_enc hk hφ
  have h1 : ((enc k φ).takeWhile id).length = n := congrArg Prod.fst h
  rw [decU, h, h1]
end CountKSat
