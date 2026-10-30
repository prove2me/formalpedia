-- Prove2me | solution 1 for DerivativeChainContinuation.positive_spoke_all_ordinary_rows
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:53:43.112754+00:00
-- url     : https://prove2.me/submissions/4827e567-eaff-488b-99e0-6777c8e0ac21

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_spoke_derivative_closed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators













theorem complex_iterate_derivative_natDegree (p : Polynomial ℂ) (j : ℕ) :
    (derivative^[j] p).natDegree=p.natDegree-j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',natDegree_derivative,ih]
    omega










end DerivativeChainContinuation

theorem solution (n k r : ℕ) (Q : Polynomial ℝ)
    (hk : 2≤k) (hQ : PositiveQuotient Q)
    (hdegree : (spokePoly k r Q).natDegree=n+1) :
    ∀ j≤n, ∃ s : ℕ, ∃ V : Polynomial ℝ, PositiveQuotient V ∧
      derivative^[j] (spokePoly k r Q)=spokePoly k s V := by
  intro j hj
  induction j with
  | zero => exact ⟨r,Q,hQ,rfl⟩
  | succ j ih =>
    obtain ⟨s,V,hV,heq⟩ := ih (by omega)
    have hd : 2≤(spokePoly k s V).natDegree := by
      rw [←heq,complex_iterate_derivative_natDegree,hdegree]
      omega
    obtain ⟨t,W,hW,hder⟩ := positive_spoke_derivative_closed k s V hk hV hd
    refine ⟨t,W,hW,?_⟩
    rw [Function.iterate_succ_apply',heq,hder]
