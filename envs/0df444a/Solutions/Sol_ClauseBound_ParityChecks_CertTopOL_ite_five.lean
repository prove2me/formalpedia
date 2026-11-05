-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertTopOL.ite_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:26:58.068322+00:00
-- url     : https://prove2.me/submissions/0de22839-b3c7-4167-a60b-e915b3aa7cf5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Inst_RecArith
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertTopOL
theorem _root_.solution {β : Type} [Enc β] {p₁ p₂ p₃ p₄ p₅ : α → Prop} [DecidablePred p₁] [DecidablePred p₂] [DecidablePred p₃] [DecidablePred p₄] [DecidablePred p₅]
    {u v : α → β} (h1 : PolyT fun x => decide (p₁ x)) (h2 : PolyT fun x => decide (p₂ x)) (h3 : PolyT fun x => decide (p₃ x)) (h4 : PolyT fun x => decide (p₄ x))
    (h5 : PolyT fun x => decide (p₅ x)) (hu : PolyT u) (hv : PolyT v) : PolyT fun x => if p₁ x ∧ p₂ x ∧ p₃ x ∧ p₄ x ∧ p₅ x then u x else v x :=
  PolyT.ite' (PolyT.decide_and h1 (PolyT.decide_and h2 (PolyT.decide_and h3 (PolyT.decide_and h4 h5)))) hu hv
end ClauseBound.ParityChecks.CertTopOL
