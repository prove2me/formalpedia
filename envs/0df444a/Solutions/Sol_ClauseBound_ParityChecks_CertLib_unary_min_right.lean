-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.unary_min_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:21:36.618791+00:00
-- url     : https://prove2.me/submissions/a549bd98-ea52-4867-9923-8b2ec74601fb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_poly


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {f g : α → ℕ} (hf : PolyT f) (hg : Unary g) : Unary fun x => min (f x) (g x) :=
  Unary.of_le hg (PolyT.min' hf hg.poly) fun _ => min_le_right _ _
end ClauseBound.ParityChecks.CertLib
