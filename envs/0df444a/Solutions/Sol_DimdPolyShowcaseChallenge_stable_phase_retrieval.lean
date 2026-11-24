-- Prove2me | solution 1 for DimdPolyShowcaseChallenge.stable_phase_retrieval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:05:33.543159+00:00
-- url     : https://prove2.me/submissions/125d120b-9e96-4cba-b35c-f5a1a83c7f06

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly
public import Theorems.Thm_DimdPolyLEAN_stablePhaseRetrievalExplicitLpClosure_ae
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyShowcaseChallenge
variable {d : ℕ}
namespace DimdPolyShowcaseChallenge
theorem _root_.solution
    (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ TrueHermitePolys κ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ Q ∈ TrueHermiteFunctions κ,
        ∃ θ : ℂ, ‖θ‖ = 1 ∧
          ∫ z, ‖P z - θ * Q z‖ ^ 2 ∂ γ
            ≤ M ^ 2 * ∫ z, (‖P z‖ - ‖Q z‖) ^ 2 ∂ γ := by
  have hTHP : TrueHermitePoly κ = DimdPolyLEAN.explicitEvalPkappa κ := by
    funext F z
    simp only [TrueHermitePoly, Φ, HermitePoly, DimdPolyLEAN.explicitEvalPkappa,
      DimdPolyLEAN.explicitPhi, DimdPolyLEAN.explicitPhi1D,
      DimdPolyLEAN.explicitComplexHermite]
  have hP' : P ∈ Set.range (DimdPolyLEAN.explicitEvalPkappa κ) := by rw [← hTHP]; exact hP
  have hγ : γ = DimdPolyLEAN.explicitGamma d := by
    simp only [γ, gaussianDensity, DimdPolyLEAN.explicitGamma,
      DimdPolyLEAN.explicitGaussianDensity, one_div]
  simp only [TrueHermiteFunctions, TrueHermitePolys, hTHP, hγ]
  exact DimdPolyLEAN.stablePhaseRetrievalExplicitLpClosure_ae (d := d) hd κ P hP'
end DimdPolyShowcaseChallenge
