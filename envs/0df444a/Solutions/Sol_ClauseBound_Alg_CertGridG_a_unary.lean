-- Prove2me | solution 1 for ClauseBound.Alg.CertGridG.a_unary
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:33:07.099055+00:00
-- url     : https://prove2.me/submissions/1de879d0-55fc-406e-b036-4f03b3ac50ac

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
variable {s : α → Step} (hs : PolyT s)
include hs
theorem solution : Unary fun x => (s x).a := by
  unfold Step.a
  exact Unary.of_length (PolyT.fst (PolyT.snd (PolyT.snd (PolyT.snd hs))))
