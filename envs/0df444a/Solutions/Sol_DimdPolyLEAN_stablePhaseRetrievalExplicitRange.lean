-- Prove2me | solution 1 for DimdPolyLEAN.stablePhaseRetrievalExplicitRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:59:47.772483+00:00
-- url     : https://prove2.me/submissions/41897a5b-a52b-4a64-9b81-2a1a0be5c106

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
public import Theorems.Thm_DimdPolyLEAN_stablePhaseRetrievalCoefficientsAll
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ Set.range (explicitEvalPkappa κ)) :
    ∃ C_P : ℝ, 0 < C_P ∧
      ∀ Q : (Fin d -> ℂ) -> ℂ, Q ∈ Set.range (explicitEvalPkappa κ) →
        ∃ θ : ℂ, ‖θ‖ = 1 ∧
          ∫ z, ‖P z - θ * Q z‖ ^ 2 ∂ explicitGamma d
            ≤ C_P ^ 2 *
              ∫ z, (‖P z‖ - ‖Q z‖) ^ 2 ∂ explicitGamma d := by
  rcases hP with ⟨F, rfl⟩
  rcases stablePhaseRetrievalCoefficientsAll hd κ F with ⟨C_P, hC_P_pos, hstable⟩
  refine ⟨C_P, hC_P_pos, ?_⟩
  simp_all
end DimdPolyLEAN
