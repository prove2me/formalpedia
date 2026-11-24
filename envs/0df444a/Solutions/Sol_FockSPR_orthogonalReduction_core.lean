-- Prove2me | solution 1 for FockSPR.orthogonalReduction_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:27.62219+00:00
-- url     : https://prove2.me/submissions/0363a1e0-774c-4603-8cc4-9c38e2ee198b

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Local
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCore
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalHelpers
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant
public import Theorems.Thm_FockSPR_LocalFockSPR_of_small_norm


set_option autoImplicit true
@[expose] public section
public section
open FockSPR MeasureTheory Complex Real Polynomial
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution
    (p : Polynomial ℂ)
    (hp_real : Complex.im (p.eval 0) = 0)
    (hsmall :
      (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        (1 / 4601 : ℝ) ^ 2) :
    ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
      23003 ^ 2 *
        ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) :=
  LocalFockSPR_of_small_norm p hp_real hsmall
end FockSPR
