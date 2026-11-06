-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertTopOL.planAtO_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:39:43.61591+00:00
-- url     : https://prove2.me/submissions/d5dd770e-d0c1-457d-8079-f3347a812d67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Inst_RecArith
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_log_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_LD_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_UbOL_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_PbOL_unary
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_restO_polyT
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_ite_five
import Theorems.Thm_ClauseBound_TopN_Cert_betaN_unary
import Theorems.Thm_ClauseBound_TopN_Cert_blockN_unary
import Theorems.Thm_ClauseBound_TopN_Cert_needNetC_polyT
import Theorems.Thm_Groundwork_PB_add
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_pow_const
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_some__e6a32bd6af45
attribute [local fun_prop] ClauseBound.TopN.Cert.betaN_unary
attribute [local fun_prop] ClauseBound.TopN.Cert.blockN_unary
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.pow_const
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
namespace ClauseBound.ParityChecks.CertTopOL
theorem _root_.solution (hP : S.Poly) (c n₀ k : ℕ) {n s : α → ℕ} {i : α → Idx} (hn : Unary n) (hi : PolyT i) (hs : Unary s) :
    PolyT fun x => planAtO S c n₀ k (n x) (i x) (s x) := by
  have hK : Unary fun x => S.K (i x) := hP.K.comp hi
  have hD := blockN_unary k hn hs
  have hU := UbOL_unary k hK hn hD
  have hQ := PbOL_unary hK hn hD
  have hr := restO_polyT k hK hn hs
  have hnet := needNetC_polyT S hP (b := fun x => List.replicate (n x) ()) hn hi hU hQ
  have hn' : PolyT n := hn.poly
  have hs' : PolyT s := hs.poly
  have hpow : PolyT fun x => 2 ^ betaN k (s x) := pow_polyT (PolyT.const 2) (betaN_unary k hs)
  have hc1 : PolyT fun x => decide (s0K k ≤ s x) := PolyT.decide_le (PolyT.const _) hs'
  have hc2 : PolyT fun x => decide (2 ^ betaN k (s x) ≤ n x + 1) := PolyT.decide_le hpow (PolyT.add hn' (PolyT.const 1))
  have hc3 : PolyT fun x => decide (n₀ ≤ n x) := PolyT.decide_le (PolyT.const _) hn'
  have hc4 : PolyT fun x => decide (2 ^ betaN k (s x) ≤ (Nat.log 2 (n x) + 1) ^ c) :=
    PolyT.decide_le hpow (((log_polyT hn').add (PolyT.const 1)).pow_const c)
  have hc5 : PolyT fun x => decide (2 * LD (2 ^ betaN k (s x)) ≤ n x) := PolyT.decide_le ((PolyT.const 2).mul (LD_polyT hpow)) hn'
  have hsum : PolyT fun q : α × ℕ => q.2 + restO k (S.K (i q.1)) (n q.1) (s q.1) :=
    PolyT.add PolyT.id'.snd (PolyT.comp (f := fun x => restO k (S.K (i x)) (n x) (s x)) hr PolyT.id'.fst)
  have hn2 : PolyT fun q : α × ℕ => n q.1 := PolyT.comp (f := n) hn' PolyT.id'.fst
  have hin : PolyT fun x => (needNetC S (List.replicate (n x) ()) (i x) (UbOL k (S.K (i x)) (n x) (blockN k (n x) (s x))) (PbOL (S.K (i x)) (n x) (blockN k (n x) (s x))) 0).bind fun v =>
      if v + restO k (S.K (i x)) (n x) (s x) ≤ n x then some (v + restO k (S.K (i x)) (n x) (s x)) else none :=
    PolyT.optionBind (PolyT.ite' (PolyT.decide_le hsum hn2) (PolyT.some' hsum) (PolyT.const none)) hnet
  unfold planAtO
  exact ite_five hc1 hc2 hc3 hc4 hc5 hin (PolyT.const none)
end ClauseBound.ParityChecks.CertTopOL
