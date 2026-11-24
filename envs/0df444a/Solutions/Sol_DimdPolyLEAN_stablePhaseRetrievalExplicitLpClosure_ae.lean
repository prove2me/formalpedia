-- Prove2me | solution 1 for DimdPolyLEAN.stablePhaseRetrievalExplicitLpClosure_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:04:18.278837+00:00
-- url     : https://prove2.me/submissions/2a40eb9a-46ff-4bdc-8951-637c7d6fd0f6

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
public import Theorems.Thm_DimdPolyLEAN_stablePhaseRetrievalExplicitLpClosure_exists
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
private theorem explicitHermiteLpPolys_eq_ae
    {d : ℕ} (κ : Fin d -> ℕ) :
    explicitHermiteLpPolys κ =
      { f : MeasureTheory.Lp ℂ 2 (explicitGamma d) |
        ∃ P ∈ Set.range (explicitEvalPkappa κ), f =ᵐ[explicitGamma d] P } := by
  ext f
  constructor
  · rintro ⟨P, hP, hP_mem, hP_toLp⟩
    subst f
    exact ⟨P, hP, hP_mem.coeFn_toLp⟩
  · rintro ⟨P, hP, hAe⟩
    have hf_mem : MeasureTheory.MemLp (f : (Fin d -> ℂ) -> ℂ) 2 (explicitGamma d) :=
      MeasureTheory.Lp.memLp f
    have hP_mem : MeasureTheory.MemLp P 2 (explicitGamma d) :=
      (MeasureTheory.memLp_congr_ae hAe).mp hf_mem
    refine ⟨P, hP, hP_mem, ?_⟩
    rw [← MeasureTheory.Lp.toLp_coeFn f hf_mem]
    exact (MeasureTheory.MemLp.toLp_eq_toLp_iff hP_mem hf_mem).2 hAe.symm
end DimdPolyLEAN
end
end
end

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
        Q ∈ closure
          { f : MeasureTheory.Lp ℂ 2 (explicitGamma d) |
            ∃ P ∈ Set.range (explicitEvalPkappa κ), f =ᵐ[explicitGamma d] P } →
          ∃ θ : ℂ, ‖θ‖ = 1 ∧
            explicitGaussianL2DistanceSq P (fun z => θ * Q z) ≤
              C_P ^ 2 * explicitModulusDistanceSq P (Q : (Fin d -> ℂ) -> ℂ) := by
  rcases stablePhaseRetrievalExplicitLpClosure_exists hd κ P hP with
    ⟨C_P, hC_P_pos, hbound⟩
  refine ⟨C_P, hC_P_pos, ?_⟩
  intro Q hQ
  exact hbound Q (by simpa [explicitHermiteLpPolys_eq_ae κ] using hQ)
end DimdPolyLEAN
