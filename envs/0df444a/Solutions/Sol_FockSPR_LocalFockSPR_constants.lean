-- Prove2me | solution 1 for FockSPR.LocalFockSPR_constants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:54.494139+00:00
-- url     : https://prove2.me/submissions/bc7bacb4-851f-4c63-a5cd-346144077a56

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalHelpers
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Local
public import Theorems.Thm_FockSPR_LocalFockSPR_of_small_norm_exists_phase


set_option autoImplicit true
@[expose] public section
public section
open FockSPR MeasureTheory Complex Real Polynomial
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution :
    ∃ δ M : ℝ,
      δ = (1 / 4601 : ℝ) ∧
      M = (23003 : ℝ) ∧
      ∀ p : Polynomial ℂ,
        (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤ δ ^ 2 →
          ∃ w : ℂ, ‖w‖ = 1 ∧
            ∫ z : ℂ, ‖w * (1 + p.eval z) - 1‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
              M ^ 2 * ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  exact ⟨(1 / 4601 : ℝ), (23003 : ℝ), rfl, rfl,
    fun p hsmall => LocalFockSPR_of_small_norm_exists_phase p hsmall⟩
end FockSPR
