-- Prove2me | solution 1 for CountKSatRate.Cert.numC_polyT_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:25:41.470553+00:00
-- url     : https://prove2.me/submissions/27ec7f8c-f9da-481f-8e5a-9d669f0012fd

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
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15



set_option autoImplicit false
section
section
open CountKSatRate
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open WidthK (theta)
open CountKSatRate.Cert
variable {α σ : Type} [Enc α]
namespace CountKSatRate.Cert
theorem _root_.solution (hW : StCertWalkS) (k : ℕ) {d : α → List Unit × Fml} {pad : α → U} {τ : α → ℕ} {val : α → CNode → ℕ} (hd : PolyT d)
    (hp : PolyT pad) (hτ : PolyT τ) (hv : PolyT fun q : α × CNode => val q.1 q.2) :
    PolyT fun p => bif hasNil (d p).2 then 0 else walkS k (pad p) (τ p) (val p) (rootC (d p)) :=
  PolyT.cond' (PolyT.comp hasNil_polyT hd.snd) (PolyT.const 0)
    (hW k α pad τ val (fun p => rootC (d p)) hp hτ hv (PolyT.comp rootC_polyT hd))
end CountKSatRate.Cert
