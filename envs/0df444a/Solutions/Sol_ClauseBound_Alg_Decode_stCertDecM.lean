-- Prove2me | solution 1 for ClauseBound.Alg.Decode.stCertDecM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:29.982222+00:00
-- url     : https://prove2.me/submissions/28dae034-e9df-4c77-9d5d-c610f08ab8f8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Definitions.Def_ClauseBound_Alg_Decode
import Theorems.Thm_ClauseBound_Alg_Decode_decU_polyT
import Theorems.Thm_ClauseBound_Alg_Decode_kOf_polyT
import Theorems.Thm_ClauseBound_Alg_Decode_restOf_polyT
import Theorems.Thm_Groundwork_Decode_width_polyT
import Theorems.Thm_Groundwork_Unary_of_length
attribute [local fun_prop] Groundwork.Decode.width_polyT



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Decode
open Groundwork CountKSat
open Groundwork.Decode (slotDec width width_polyT)
open Groundwork.DecodeK (clauseDec decK)
variable {α : Type} [Enc α]
namespace ClauseBound.Alg.Decode
theorem _root_.solution : StCertDecM :=
  ⟨kOf_polyT, decU_polyT (Unary.of_length kOf_polyT) restOf_polyT⟩
end ClauseBound.Alg.Decode
