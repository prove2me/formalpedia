-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.germ_in_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:42:21.64553+00:00
-- url     : https://prove2.me/submissions/8bf815c5-460e-40a6-ae97-6f23618d7858

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux8_zero_notMem_detSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution (hG : G.GermRate) (hD : G.DetMatch) (hU : UseDerivBound) (hS : ScaleMatch) :
    ∃ (C₂ : ℕ) (Cc : ℝ),
    ∀ (k p m ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ι : Type) [Fintype ι]
    (U : UData k p (m+1+1) ρ Wp Wq ι), U.Ok C₂ →
    ∀ A₀ : ℝ, Cc * (((p + (m+1+1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (U.As : ℝ) ≤ A₀ →
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc → ∃ Cst : ℝ,
    ∀ (bet : (B.Mat k ρ → ι → (Wq →L[ℂ] Wp)) → (B.Mat k ρ → ι → (Wq →L[ℂ] Wp)) → ℂ) (Cp : ℝ), 0 ≤ Cp →
      PosP bet (U.a C₂ A₀) U.mmB U.S → LBound bet U.AB U.mmB U.S Cp →
      (∀ x y x' y' : B.Mat k ρ → ι → (Wq →L[ℂ] Wp), (∀ g ∈ B.GV k ρ, x g = x' g) → (∀ g ∈ B.GV k ρ, y g = y' g) →
        bet x y = bet x' y') →
      ∀ (f : B.Mat k (p + (m+1+1) + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ (3 * U.As) f c →
      ∃ (V' : Type) (_ : NormedAddCommGroup V') (_ : NormedSpace ℂ V'), CompleteSpace V' ∧ ∃ Φ' : G.Mat (m+1+1) → V',
        (∀ (J : Finset (G.Mat (m+1+1))) (w : G.Mat (m+1+1) → ℂ), (∀ Z ∈ J, G.detM Z ≠ 0) →
          ‖∑ Z ∈ J, w Z • Φ' Z‖ ^ 2 = (bet (∑ Z ∈ J, w Z • U.Phi f Z) (∑ Z ∈ J, w Z • U.Phi f Z)).re) ∧
        ∀ t c' : ℂ, t ≠ 0 → c' * t ^ (m+1) ∈ Kc →
          ‖G.remainder betaU m (fun _ => 1) Φ' t c'‖ ≤ Cst * Cp * c * ‖t‖ := by
  obtain ⟨C₁, C₂, hGR⟩ := hG
  obtain ⟨Cc, hCc⟩ := hU C₁ C₂
  refine ⟨C₂, Cc, ?_⟩
  intro k p m ρ Wp Wq _ _ _ _ _ _ ι _ U hOk A₀ hA₀ Kc hKc h0
  obtain ⟨_, twice_smooth_le_first, _, C, hC⟩ := hCc k p (m + 1 + 1) ρ Wp Wq ι U hOk A₀ hA₀
  obtain ⟨_, hβ, _⟩ := hS
  obtain ⟨Cst, hCst⟩ := hGR m betaU hβ Kc hKc h0
  refine ⟨Cst * C, ?_⟩
  intro bet Cp hCp hPos hLB hcong f c hf
  obtain ⟨V', i1, i2, hcomp, Φ', hnorm, hDBd⟩ := hC bet Cp hCp hPos hLB hcong f c hf
  refine ⟨V', i1, i2, hcomp, Φ', hnorm, ?_⟩
  intro t c' ht hc'
  have hA' : (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 ≤ U.a C₂ A₀ := by
    have e : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    rw [e] at twice_smooth_le_first
    exact twice_smooth_le_first
  have hfin := hCst V' Φ' (U.a C₂ A₀) (C * Cp * c) (C₂ * (m + 1 + 1) ^ 2) hA' (le_of_eq (by ring))
    (hDBd _ (zero_notMem_detSet hD (m + 1) Kc h0)) t c' ht hc'
  calc _ ≤ Cst * (C * Cp * c) * ‖t‖ := hfin
    _ = Cst * C * Cp * c * ‖t‖ := by ring
end Formalism.FourierDecayAlt.P.Ux8
