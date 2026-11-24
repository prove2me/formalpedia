-- Prove2me | solution 1 for FockSPR.orthogonalReduction_exists_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:47.31717+00:00
-- url     : https://prove2.me/submissions/2340f54f-ba0e-4b1a-92a6-693cb64d6048

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Local
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCore
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalHelpers
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant
public import Theorems.Thm_FockSPR_LocalFockSPR_of_small_norm_exists_phase


set_option autoImplicit true
@[expose] public section
public section
open FockSPR MeasureTheory Complex Real Polynomial
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution
    (p : Polynomial ℂ)
    (hsmall :
      (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        (1 / 4601 : ℝ) ^ 2) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      ∫ z : ℂ, ‖w * ((1 : ℂ) + p.eval z) - 1‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        23003 ^ 2 *
          ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) :=
  LocalFockSPR_of_small_norm_exists_phase p hsmall
end FockSPR
