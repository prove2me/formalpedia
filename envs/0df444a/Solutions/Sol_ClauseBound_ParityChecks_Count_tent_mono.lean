-- Prove2me | solution 1 for ClauseBound.ParityChecks.Count.tent_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:14:01.038021+00:00
-- url     : https://prove2.me/submissions/261d4896-2bde-4a69-a4ed-8300a2b3b897

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_ClauseBound_ParityChecks_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Count
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks
namespace ClauseBound.ParityChecks.Count
theorem _root_.solution {q : Par} {Λ Λ' : ℕ → Finset (Fin q.m)} (h : ∀ j, Λ' j ⊆ Λ j) (hT : Tent q Λ) : Tent q Λ' where
  inc := by
    refine lt_of_le_of_lt ?_ hT.inc
    exact_mod_cast Finset.sum_le_sum fun j _ => Finset.card_le_card (h j)
  row j' hj' := lt_of_le_of_lt (pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (h j'))) (hT.row j' hj')
  col x := by
    refine lt_of_le_of_lt (pow_le_pow_right₀ (by norm_num) (Finset.card_le_card ?_)) (hT.col x)
    intro j' hj'
    rw [Finset.mem_filter] at hj' ⊢
    exact ⟨hj'.1, h j' hj'.2⟩
end ClauseBound.ParityChecks.Count
