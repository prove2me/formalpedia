-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertPar.parQ_QU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:29:42.194643+00:00
-- url     : https://prove2.me/submissions/86bde03c-98c8-4579-a48b-fa8f78399984

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_nbOf_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_beta0_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_rOf_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_i0Of_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_beta1_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_parQ_m
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_parQ_nb
import Theorems.Thm_ClauseBound_ParityChecks_CertPar_parQ_r
import Theorems.Thm_P2M_ClauseBound_ParityChecks_CertPar_parQ_i__93c9d582f9ae
import Theorems.Thm_P2M_ClauseBound_ParityChecks_CertPar_parQ___e24fc9b201b1
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_congr
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_ite
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_congr
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] ClauseBound.Alg.CertGridG.unary_ite
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertPar
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertPar
theorem _root_.solution {n Δ m : α → ℕ} (hn : Unary n) (hΔ : Unary Δ) (hm : Unary m) : QU fun x => parQ (n x) (Δ x) (m x) := by
  have hnb := nbOf_unary hn hΔ.poly
  have hb0 := beta0_unary hm.poly hnb
  have hi0 := i0Of_unary hn
  exact
    { m := unary_congr hm fun x => (parQ_m _ _ _).symm
      nb := unary_congr hnb fun x => (parQ_nb _ _ _).symm
      r := unary_congr (ClauseBound.Alg.CertGridG.unary_ite (PolyT.decide_le hm.poly hnb.poly) (Unary.const 0) (rOf_unary hn hb0)) fun x => (parQ_r _ _ _).symm
      i₀ := unary_congr hi0 fun x => (parQ_i₀ _ _ _).symm
      β := unary_congr (((hn.add hb0).add (beta1_unary hm.poly hi0)).add (Unary.const 2)) fun x => (parQ_β _ _ _).symm }
end ClauseBound.ParityChecks.CertPar
