-- Prove2me | solution 1 for CountKSatRate.Cert.nK_unary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:34:53.703695+00:00
-- url     : https://prove2.me/submissions/d0e45b9f-7a5b-4a24-a6cf-1aead6aeb0f3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_InOut
import Definitions.Def_PaddedDescent_F_CertA
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_PaddedDescent_F_CertSide
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_CountKSatRate_Cert
import Theorems.Thm_CountKSatRate_Cert_decU_pad_polyT
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_Unary_of_length
attribute [local fun_prop] Groundwork.PolyT.fst



set_option autoImplicit false
section
section
open CountKSatRate
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open WidthK (theta)
open Cert
namespace CountKSatRate
namespace Cert
theorem _root_.solution (k : ℕ) : Unary fun p : List Bool × U => nK k p.1 := Unary.of_length (decU_pad_polyT k).fst
end Cert
end CountKSatRate
