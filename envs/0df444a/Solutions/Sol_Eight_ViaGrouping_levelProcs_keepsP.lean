-- Prove2me | solution 1 for Eight.ViaGrouping.levelProcs_keepsP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:38:46.203786+00:00
-- url     : https://prove2.me/submissions/56d4d3f1-41a8-4d78-8d99-b3593de4e65d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_Level_Cert
import Definitions.Def_Eight_ViaGrouping_LevelCert
import Theorems.Thm_Eight_Level_stNetKeeps_of
import Theorems.Thm_Eight_ViaGrouping_keepsP_ofProcs
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg Stepped Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (h : Eight.StKeeps) (g : ℕ) (tr : Bool) {psi : ℕ → ℕ → PsiQ → ℤ} (hp : StPsiPoly psi) (C : Type) [HasSize C] [Enc C] [Carried C] (lam : C → ℕ)
    (R : Stepped (C × IQ) ℤ) (hl : Unary lam) (hR : Nonempty (IsPolyT R)) : KeepsP (levelProcs g tr psi lam R) :=
  keepsP_ofProcs (stNetKeeps_of h g tr C lam R hl hR) ((Unary.const (g ^ 3)).mul (hl.comp (h := fun c : C × ℕ => c.1) PolyT.id'.fst)) ⟨IsPolyT.ofFun (hp C lam hl)⟩
end Eight.ViaGrouping
