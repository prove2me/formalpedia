-- Prove2me | solution 1 for DimdPolyLEAN.stablePhaseRetrievalCoefficientsAll
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:52.452999+00:00
-- url     : https://prove2.me/submissions/fc7f5ad3-73e7-43f7-b90c-76dd1d0c8c3a

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
public import Theorems.Thm_DimdPolyLEAN_stablePhaseRetrievalCoefficients
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
    (F : Finsupp (Fin d -> ℕ) ℂ) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ Q : Finsupp (Fin d -> ℕ) ℂ,
        ∃ θ : ℂ, ‖θ‖ = 1 ∧
          ∫ z, ‖explicitEvalPkappa κ F z - θ * explicitEvalPkappa κ Q z‖ ^ 2
              ∂ explicitGamma d
            ≤ C_F ^ 2 *
              ∫ z, (‖explicitEvalPkappa κ F z‖ - ‖explicitEvalPkappa κ Q z‖) ^ 2
                ∂ explicitGamma d := by
  by_cases hF : F = 0
  · subst F
    refine ⟨1, by norm_num, ?_⟩
    intro Q
    refine ⟨1, by simp, ?_⟩
    simp [explicitEvalPkappa]
  · exact stablePhaseRetrievalCoefficients hd κ F hF
end DimdPolyLEAN
