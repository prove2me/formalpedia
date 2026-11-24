-- Prove2me | solution 1 for FockSPR.centeredPolynomial_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:24.87774+00:00
-- url     : https://prove2.me/submissions/81172f84-0325-4d3c-b91e-78401f2fdfb5

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Local
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCore
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalHelpers
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant

set_option autoImplicit true
@[expose] public section
public section
open FockSPR MeasureTheory Complex Real Polynomial
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution (p : Polynomial ℂ) :
    (centeredPolynomial p).eval 0 = 0 := by simp [centeredPolynomial]
end FockSPR
