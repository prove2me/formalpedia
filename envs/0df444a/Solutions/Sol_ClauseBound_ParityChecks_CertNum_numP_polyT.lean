-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertNum.numP_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:34:44.129968+00:00
-- url     : https://prove2.me/submissions/04cd8fe1-87e6-48a2-8098-a37b600696ab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Theorems.Thm_ClauseBound_ParityChecks_CertNum_numP_aux

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertNum
open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertNum
theorem _root_.solution {q : α → Par} (hq : QU q) {A : α → ℤ} {B : α → ℕ → ℤ} (hA : PolyT A) (hB : PolyT fun p : α × ℕ => B p.1 p.2) :
    PolyT fun x => (q x).numP (A x) (B x) := by
  unfold Par.numP
  exact numP_aux hq.nb hq.i₀ hA hB
end ClauseBound.ParityChecks.CertNum
