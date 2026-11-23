-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G3.double_vol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:32.822733+00:00
-- url     : https://prove2.me/submissions/85591b47-cdc7-4acd-9e07-5f30ca7f9ea9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_integral_comp_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_integral_comp_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_norm_al
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_phase2
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_inner_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P.G3
theorem _root_.solution (β : ℂ) (hβ : β ≠ 0) (f : SchwartzMap ℂ ℂ) (w : ℂ) :
    ∫ ξ : ℂ, (∫ x : ℂ, f x * psi β (ξ * x)) * psi β (w * ξ) =
      (((‖β‖ / (2 * Real.pi)) ^ 2)⁻¹ : ℝ) • f (-w) := by
  have hα : al β ≠ 0 := by
    rw [← norm_pos_iff, norm_al]
    have := norm_pos_iff.mpr hβ
    positivity
  have hinv : 𝓕⁻ (𝓕 (f : ℂ → ℂ)) = f :=
    f.continuous.fourierInv_fourier_eq f.integrable (𝓕 f).integrable
  set G : ℂ → ℂ := fun η =>
    Complex.exp ((↑(2 * Real.pi * ⟪η, -w⟫) * Complex.I)) • 𝓕 (f : ℂ → ℂ) η with hG
  have h1 : ∀ ξ : ℂ, (∫ x : ℂ, f x * psi β (ξ * x)) * psi β (w * ξ) =
      G (al β * (starRingEnd ℂ) ξ) := by
    intro ξ
    rw [inner_int, hG]
    simp only [phase2, psi, smul_eq_mul]
    rw [mul_comm, mul_comm Complex.I]
  simp_rw [h1]
  rw [integral_comp_conj (fun η => G (al β * η)), integral_comp_mul _ hα, norm_al, hG,
    ← Real.fourierInv_eq', hinv]
end Formalism.FourierDecayAlt.P.G3
