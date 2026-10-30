-- Prove2me | solution 1 for DerivativeChainContinuation.coefficient_gap_four_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:11:55.991978+00:00
-- url     : https://prove2.me/submissions/ede78871-4209-4930-b8b7-07fa2564f838

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainContinuation_coefficient_gap_chain_bound
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false



set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (p : Polynomial ℂ) (hp : p.Monic) (n h k : ℕ)
    (hn : p.natDegree=n) (hh : 1 ≤ h) (hh15 : h ≤ 15) (hhk : h ≤ k) (hk : k ≤ n-2)
    (A : ℂ) (Q : Polynomial ℂ) (hQ : Q.natDegree < h)
    (hgap : centeredSource p=X^n+C A*X^k+Q)
    (hbound : ∀ z : ℂ, p.eval z=0 → ‖z‖ ≤ 1) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,by omega⟩=rootCentroid p ∧ chainCost z ≤ 4 := by
  obtain ⟨z,hzr,hz0,hzc,_⟩ := coefficient_gap_chain_bound p hp n h k hn hh hhk hk A Q hQ
    hgap 1 (by norm_num) hbound
  have h1 : Real.sqrt (h+1) ≤ 4 := by
    have hs := Real.sqrt_le_sqrt (show (h+1:ℝ) ≤ 16 by exact_mod_cast (show h+1 ≤ 16 by omega))
    norm_num at hs
    exact hs
  have h2 : Real.sqrt ((1:ℝ)^2-‖rootCentroid p‖^2) ≤ 1 := by
    have hs := Real.sqrt_le_sqrt (show (1:ℝ)^2-‖rootCentroid p‖^2 ≤ 1 by nlinarith [sq_nonneg ‖rootCentroid p‖])
    simpa using hs
  refine ⟨z,hzr,hz0,hzc.trans ?_⟩
  have hm := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 4)
  simpa using hm
