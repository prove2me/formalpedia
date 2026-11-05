-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.QU.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:37:13.707037+00:00
-- url     : https://prove2.me/submissions/dc2c0639-7551-4899-9bb7-af9ced1f28be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_Unary_comp
attribute [local fun_prop] Groundwork.PolyT.comp



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
namespace QU
theorem _root_.solution {β : Type} [Enc β] {q : α → Par} (hq : QU q) {g : β → α} (hg : PolyT g) : QU fun y => q (g y) :=
  ⟨hq.m.comp hg, hq.nb.comp hg, hq.r.comp hg, hq.i₀.comp hg, hq.β.comp hg⟩
end QU
end ClauseBound.ParityChecks.CertLib
