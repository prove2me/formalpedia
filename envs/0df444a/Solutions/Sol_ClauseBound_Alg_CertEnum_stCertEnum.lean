-- Prove2me | solution 1 for ClauseBound.Alg.CertEnum.stCertEnum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:59:46.554952+00:00
-- url     : https://prove2.me/submissions/ccb8c9d1-574f-4167-8b48-94f50bbbb5fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertEnum
import Theorems.Thm_ClauseBound_Alg_CertEnum_enumF_polyT

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertEnum
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertNet
variable {α : Type} [Enc α] {C : Type} [Enc C] {F : FNet C}
namespace ClauseBound.Alg.CertEnum
theorem _root_.solution : StCertEnum := fun _ _ _ hF _ _ _ _ _ hp hg hc => enumF_polyT hF hp hg hc
end ClauseBound.Alg.CertEnum
