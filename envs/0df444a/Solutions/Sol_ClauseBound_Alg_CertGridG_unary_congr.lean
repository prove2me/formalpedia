-- Prove2me | solution 1 for ClauseBound.Alg.CertGridG.unary_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:16:13.662819+00:00
-- url     : https://prove2.me/submissions/903ba4c6-3b26-4ab9-9bd4-2a20a9d39015

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.Alg.CertGridG
theorem _root_.solution {f g : α → ℕ} (h : Unary f) (e : ∀ x, f x = g x) : Unary g := by
  obtain rfl : f = g := funext e
  exact h
end ClauseBound.Alg.CertGridG
