-- Prove2me | solution 1 for DerivativeChainContinuation.at_most_two_centered_modes_unit_disk
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:06:59.057444+00:00
-- url     : https://prove2.me/submissions/ba5aae3a-c70b-4ce8-b518-ec0a89d5c70d

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainContinuation_TwoModeChain
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainContinuation_at_most_two_centered_modes_chain
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
theorem solution (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hn : p.natDegree=n) (hnpos : 0 < n)
    (hmodes : (centeredModeSupport p).card ≤ 2)
    (hbound : ∀ z : ℂ, p.eval z=0 → ‖z‖ ≤ 1) :
    ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      z ⟨0,hnpos⟩=rootCentroid p ∧ chainCost z ≤ 1+Real.sqrt 2 := by
  obtain ⟨z,hzr,hz0,hzc⟩ := at_most_two_centered_modes_chain p hp n hn hnpos hmodes
    0 1 (by norm_num) (fun z hz => by simpa using hbound z hz)
  have hrad : Real.sqrt ((1:ℝ)^2-‖rootCentroid p-0‖^2) ≤ 1 := by
    have hh := Real.sqrt_le_sqrt (show (1:ℝ)^2-‖rootCentroid p-0‖^2 ≤ 1 by nlinarith [sq_nonneg ‖rootCentroid p-0‖])
    simpa using hh
  refine ⟨z,hzr,hz0,hzc.trans ?_⟩
  simpa using mul_le_mul_of_nonneg_left hrad (by positivity : (0:ℝ) ≤ 1+Real.sqrt 2)
