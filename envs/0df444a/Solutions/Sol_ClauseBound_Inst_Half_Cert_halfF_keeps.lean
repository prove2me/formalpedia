-- Prove2me | solution 1 for ClauseBound.Inst.Half.Cert.halfF_keeps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:44:41.118255+00:00
-- url     : https://prove2.me/submissions/dc61b112-c87a-4ce3-afbc-1a94cc373176

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
import Theorems.Thm_ClauseBound_Inst_Half_Cert_partH_polyT
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_bits
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_cap
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_cnt
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_need


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.Cert
theorem _root_.solution (c₀ c : ℕ) : (halfF c₀ c).Keeps :=
  ⟨CertSmall.cnt c₀ c, CertSmall.d c₀ c, CertSmall.cap c₀ c, partH_polyT c₀ true, partH_polyT c₀ false, CertSmall.need c₀ c, CertSmall.bits c₀ c⟩
end ClauseBound.Inst.Half.Cert
