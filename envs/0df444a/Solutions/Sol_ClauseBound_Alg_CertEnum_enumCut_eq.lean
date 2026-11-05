-- Prove2me | solution 1 for ClauseBound.Alg.CertEnum.enumCut_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:36.2432+00:00
-- url     : https://prove2.me/submissions/76d60248-c62d-4b5b-8269-3fcdabb03efe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertEnum
import Theorems.Thm_ClauseBound_Alg_CertEnum_prodL_congr
import Theorems.Thm_ClauseBound_Alg_CertEnum_chunkCut_eq
import Theorems.Thm_ClauseBound_Alg_CertEnum_pair_le
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertEnum
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertNet
variable {α : Type} [Enc α] {C : Type} [Enc C] {F : FNet C}
omit [Enc C]
namespace ClauseBound.Alg.CertEnum
theorem _root_.solution (pad : U) (g : ℕ) (F : FNet C) (c : C) : enumCut pad g F c = enumF pad g F c := by
  unfold enumCut enumF
  congr 1
  funext t
  refine prodL_congr fun a ha => ?_
  congr 1
  funext zi
  congr 1
  refine prodL_congr fun b hb => ?_
  rw [chunkCut_eq F c (pair_le ha hb)]
end ClauseBound.Alg.CertEnum
