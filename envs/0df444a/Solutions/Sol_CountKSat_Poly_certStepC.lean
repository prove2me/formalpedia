-- Prove2me | solution 1 for CountKSat.Poly.certStepC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:55:07.729708+00:00
-- url     : https://prove2.me/submissions/c7fd3020-c431-497d-9168-0ae054d3f5f8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Walk
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_CountKSat_Poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open CountKSat CountKSat.Poly
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog Groundwork.Stepped
variable {α : Type}
namespace CountKSat.Poly
theorem _root_.solution : StCertStepC := fun θ k => polyT_stepC θ k PolyT.id'
end CountKSat.Poly
