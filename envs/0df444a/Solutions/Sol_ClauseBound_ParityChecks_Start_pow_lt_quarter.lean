-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.pow_lt_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:11:14.759409+00:00
-- url     : https://prove2.me/submissions/3b267fe5-6bbc-4aea-a30a-5afa46afb0b7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution (nb v : ℕ) (hnb : 2 ≤ nb) (hv : nb < v) : ((1 : ℝ) - 2 / nb) ^ v < 1 / 4 := by
  have hn : (0 : ℝ) < nb := by exact_mod_cast (by omega : 0 < nb)
  have hn2 : (2 : ℝ) ≤ nb := by exact_mod_cast hnb
  have h0 : 0 ≤ (1 : ℝ) - 2 / nb := by rw [sub_nonneg, div_le_one hn]; exact hn2
  have h1 : (1 : ℝ) - 2 / nb ≤ Real.exp (-(2 / nb)) := Real.one_sub_le_exp_neg _
  have h2 : ((1 : ℝ) - 2 / nb) ^ v ≤ Real.exp (-(2 / nb)) ^ v := pow_le_pow_left₀ h0 h1 v
  have h3 : Real.exp (-(2 / nb)) ^ v = Real.exp (v * (-(2 / nb))) := (Real.exp_nat_mul _ _).symm
  have h4 : (v : ℝ) * (-(2 / nb)) < -2 := by
    have hv' : (nb : ℝ) < v := by exact_mod_cast hv
    have h5 : 1 < (v : ℝ) / nb := by rwa [one_lt_div hn]
    have e : (v : ℝ) * (-(2 / nb)) = -2 * (v / nb) := by ring
    rw [e]; linarith
  have h5 : Real.exp (v * (-(2 / nb))) < Real.exp (-2) := Real.exp_lt_exp.2 h4
  have h6 : Real.exp (-2) ≤ 1 / 4 := by
    have e1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have e3 : 4 ≤ Real.exp 2 := by rw [e2]; nlinarith
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) e3
  rw [h3] at h2
  linarith
end ClauseBound.ParityChecks.Start
