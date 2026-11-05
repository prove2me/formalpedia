-- Prove2me | solution 1 for ClauseBound.Alg.Decode.stDecM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:41:50.611202+00:00
-- url     : https://prove2.me/submissions/f89d68d9-a68f-44de-b882-9148c2278025

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Definitions.Def_ClauseBound_Alg_Decode
import Theorems.Thm_ClauseBound_Alg_Decode_kOf_ones
import Theorems.Thm_ClauseBound_Alg_Decode_restOf_ones
import Theorems.Thm_CountKSat_stDecU
import Theorems.Thm_Groundwork_Decode_width_polyT
attribute [local fun_prop] Groundwork.Decode.width_polyT



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Decode
open Groundwork CountKSat
open Groundwork.Decode (slotDec width width_polyT)
open Groundwork.DecodeK (clauseDec decK)
namespace ClauseBound.Alg.Decode
theorem _root_.solution : StDecM := fun k n φ hk hφ => by
  refine ⟨kOf_ones k _, ?_⟩
  rw [fmlOf, SatM.enc, kOf_ones, restOf_ones, List.length_replicate]
  exact stDecU k n φ hk hφ
end ClauseBound.Alg.Decode
