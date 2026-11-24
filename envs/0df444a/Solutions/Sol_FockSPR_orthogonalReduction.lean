-- Prove2me | solution 1 for FockSPR.orthogonalReduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:25.351735+00:00
-- url     : https://prove2.me/submissions/761c6520-495f-402b-b526-40b464cf97ee

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
    p = centeredPolynomial p + Polynomial.C (p.eval 0) := by
  simp [centeredPolynomial, sub_add_cancel]
end FockSPR
