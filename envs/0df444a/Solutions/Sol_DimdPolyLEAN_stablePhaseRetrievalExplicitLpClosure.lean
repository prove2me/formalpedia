-- Prove2me | solution 1 for DimdPolyLEAN.stablePhaseRetrievalExplicitLpClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:02:18.565166+00:00
-- url     : https://prove2.me/submissions/9dc1f28c-2e37-45ea-8866-c8901df445d8

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
public import Theorems.Thm_DimdPolyLEAN_stablePhaseRetrievalExplicitClosure
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
      ∀ Q : MeasureTheory.Lp ℂ 2 (explicitGamma d),
        Q ∈ closure (explicitHermiteLpPolys κ) →
          explicitPhaseOptimizedDistanceSq P (Q : (Fin d -> ℂ) -> ℂ) ≤
            C_P ^ 2 * explicitModulusDistanceSq P (Q : (Fin d -> ℂ) -> ℂ) := by
  rcases stablePhaseRetrievalExplicitClosure hd κ P hP with ⟨C_P, hC_P_pos, hbound⟩
  refine ⟨C_P, hC_P_pos, ?_⟩
  intro Q hQ
  have hQ_raw :
      (Q : (Fin d -> ℂ) -> ℂ) ∈ explicitClosureOfHermitePolys κ := by
    refine ⟨MeasureTheory.Lp.memLp Q, ?_⟩
    simpa [explicitClosureOfHermitePolys] using hQ
  exact hbound (Q : (Fin d -> ℂ) -> ℂ) hQ_raw
end DimdPolyLEAN
