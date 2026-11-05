-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.unary_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:52:35.842125+00:00
-- url     : https://prove2.me/submissions/053e38c3-2853-4c51-aad5-7e1b876248f6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {f g : α → ℕ} (h : Unary f) (e : ∀ x, f x = g x) : Unary g := by
  obtain rfl : f = g := funext e
  exact h
end ClauseBound.ParityChecks.CertLib
