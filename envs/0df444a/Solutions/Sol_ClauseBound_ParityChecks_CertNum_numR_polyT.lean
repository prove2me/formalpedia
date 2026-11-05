-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertNum.numR_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:33:22.110616+00:00
-- url     : https://prove2.me/submissions/465c5cff-fbd6-462b-8487-dfd00c27a9be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Theorems.Thm_ClauseBound_ParityChecks_CertNum_numR_aux

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertNum
open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertNum
theorem _root_.solution {q : α → Par} (hq : QU q) {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hL : PolyT Ls) (hc : PolyT cur) (he : Unary e) :
    PolyT fun x => (q x).numR (Ls x) (cur x) (e x) := by
  unfold Par.numR Par.k
  exact numR_aux hq.m hq.nb hq.r hL hc he
end ClauseBound.ParityChecks.CertNum
