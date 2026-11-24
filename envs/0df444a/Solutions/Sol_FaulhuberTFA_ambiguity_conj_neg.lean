-- Prove2me | solution 1 for FaulhuberTFA.ambiguity_conj_neg
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:09:03.100012+00:00
-- url     : https://prove2.me/submissions/36dab2be-6016-44bf-9db9-c59b0aaccb18

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

set_option autoImplicit false

open MeasureTheory Complex
open scoped InnerProductSpace
open FaulhuberTFA

private lemma conj_ePhase (s : ℝ) : starRingEnd ℂ (ePhase s) = ePhase (-s) := by
  unfold ePhase; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

theorem solution {d : ℕ} {f : Rd d → ℂ} (hf : MemLp f 2 volume) (x ω : Rd d) :
    starRingEnd ℂ (ambiguity f (-x) (-ω)) = ambiguity f x ω := by
  unfold ambiguity crossAmbiguity
  rw [← integral_conj]
  congr 1; funext t
  simp only [map_mul, Complex.conj_conj, conj_ePhase, smul_neg, sub_neg_eq_add, ← sub_eq_add_neg,
    inner_neg_left, neg_neg]
  ring
