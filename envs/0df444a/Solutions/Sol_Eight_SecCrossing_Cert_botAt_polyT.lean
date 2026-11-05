-- Prove2me | solution 1 for Eight.SecCrossing_Cert.botAt_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:09:40.902548+00:00
-- url     : https://prove2.me/submissions/4c8470a7-0c82-4298-ada7-376db9bd947d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_MulOut
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_Eight_SecCrossing_Cert
import Theorems.Thm_Eight_SecCrossing_Cert_blkAt_polyT
import Theorems.Thm_Eight_SecCrossing_Cert_blkL_polyT
import Theorems.Thm_Eight_SecCrossing_Cert_psi_polyT
import Theorems.Thm_Eight_SecCrossing_Cert_Rb_polyT
import Theorems.Thm_Eight_SecCrossing_Cert_wide_polyT
import Theorems.Thm_Eight_SecCrossing_Cert_off_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219



set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F ClauseBound.Alg SingleBitPieces.SecCrossing_PolyA
open Eight.SecCrossing_Cert
variable {α : Type} [Enc α]
namespace Eight.SecCrossing_Cert
theorem _root_.solution {tr : α → Bool} {Q w a b : α → List Bool} {s : α → ℕ} (htr : PolyT tr) (hQ : PolyT Q) (hw : PolyT w) (ha : PolyT a) (hb : PolyT b)
    (hs : Unary s) : PolyT fun x => botAt (tr x) (Q x) (w x) (a x) (b x) (s x) := by
  have ho := off_polyT htr hQ hs
  have h1 := blkAt_polyT hw ho
  have h2 := blkAt_polyT hw (PolyT.add ho (PolyT.const 3))
  have h3 := blkL_polyT ha hs.poly
  have h4 := blkL_polyT hb hs.poly
  unfold botAt
  exact PolyT.ite' (PolyT.decide_eq (wide_polyT htr hQ hs.poly) (PolyT.const true)) (Rb_polyT h1 h3 h2 h4) (psi_polyT h1 h4 h3)
end Eight.SecCrossing_Cert
