-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.roots_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:06.070953+00:00
-- url     : https://prove2.me/submissions/e107745e-0627-49be-84c1-943536d0ec84

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (μ : Finset Kˣ) (hμ : ∀ ζ : Kˣ, ζ ∈ μ ↔ ζ ^ (m + 1) = 1)
    (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite) (D z₀ : Kˣ) (hz₀ : z₀ ^ (m + 1) = D)
    (G : Kˣ → ℂ) : ∑ z ∈ (hroots D).toFinset, G z = ∑ ζ ∈ μ, G (ζ * z₀) := by
  symm
  apply Finset.sum_bij (fun ζ _ => ζ * z₀)
  · intro ζ hζ
    simp [mul_pow, (hμ ζ).1 hζ, hz₀]
  · intro a _ b _ hab
    exact mul_right_cancel hab
  · intro z hz
    have hz' : z ^ (m + 1) = D := by simpa using hz
    refine ⟨z * z₀⁻¹, (hμ _).2 ?_, by simp⟩
    rw [mul_pow, inv_pow, hz', hz₀, mul_inv_cancel]
  · intros
    rfl
end Formalism.FourierDecayAlt.P.GermSumLattices
