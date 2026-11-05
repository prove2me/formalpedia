-- Prove2me | solution 1 for ClauseBound.Alg.CertEnum.pair_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:40:13.199914+00:00
-- url     : https://prove2.me/submissions/23189de1-30cd-47fe-8dbd-c23830bb7600

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertEnum

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertEnum
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertNet
variable {α : Type} [Enc α] {C : Type} [Enc C] {F : FNet C}
namespace ClauseBound.Alg.CertEnum
theorem _root_.solution {g a b : ℕ} (ha : a < g) (hb : b < g) : min a b * g + max a b ≤ g * g := by
  have h1 : min a b + 1 ≤ g := by omega
  have h2 : max a b ≤ g := by omega
  calc min a b * g + max a b ≤ min a b * g + g := Nat.add_le_add_left h2 _
    _ = (min a b + 1) * g := by ring
    _ ≤ g * g := Nat.mul_le_mul_right _ h1
end ClauseBound.Alg.CertEnum
