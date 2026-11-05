-- Prove2me | solution 1 for ClauseBound.Inst.Half.CertSmall.d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:00:25.22958+00:00
-- url     : https://prove2.me/submissions/2f8a7291-2811-4500-bc83-62ded72fdce1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Theorems.Thm_ClauseBound_Inst_Half_hF_unary
import Theorems.Thm_ClauseBound_Inst_Rec_factN_polyT
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] ClauseBound.Inst.Rec.factN_polyT
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.CertSmall
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.CertSmall
theorem _root_.solution (c₀ c : ℕ) : PolyT fun p : U × U => (halfF c₀ c).d p.1.length p.2.length :=
  factN_polyT (hF_unary c₀ (Unary.of_length PolyT.id'.snd))
end ClauseBound.Inst.Half.CertSmall
