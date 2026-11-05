-- Prove2me | solution 1 for ClauseBound.ParityChecks.Ev.sized_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:08:59.249511+00:00
-- url     : https://prove2.me/submissions/28f68356-92a8-4a4d-9616-64019fbd1a59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Ev
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Ev
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW
namespace ClauseBound.ParityChecks.Ev
theorem _root_.solution {J σ τ : Type} [Fintype J] [LinearOrder J] {N : Network J σ τ} {P P' B : ℕ} (h : N.Sized P B) (hP : P ≤ P') : N.Sized P' B where
  card_S a := (h.card_S a).trans (Nat.pow_le_pow_right (by norm_num) hP)
  c_symm := h.c_symm
  sum_c a := (h.sum_c a).trans hP
  card_lab := h.card_lab
  abs_W := h.abs_W
  abs_f := h.abs_f
  abs_Ψ := h.abs_Ψ
end ClauseBound.ParityChecks.Ev
