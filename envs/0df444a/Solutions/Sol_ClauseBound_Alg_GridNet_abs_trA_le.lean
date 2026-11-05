-- Prove2me | solution 1 for ClauseBound.Alg.GridNet.abs_trA_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:07:44.442002+00:00
-- url     : https://prove2.me/submissions/daf238c4-183d-4542-a617-3da39488fdd7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {P : PiecesF} {pad : U} {h ℓ : ℕ} {A : ℕ → Pieces.Four ℓ}
namespace ClauseBound.Alg.GridNet
theorem _root_.solution {b : ℕ} {F : Pieces.Four ℓ} (hF : ∀ x y u v, |F x y u v| ≤ 2 ^ b) (tr : Bool) (x y u v : Bits ℓ) :
    |trA tr F x y u v| ≤ 2 ^ b := by
  cases tr
  · exact hF x y u v
  · exact hF x u y v
end ClauseBound.Alg.GridNet
