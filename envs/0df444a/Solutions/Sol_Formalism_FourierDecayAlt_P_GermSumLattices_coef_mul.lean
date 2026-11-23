-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.coef_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:32.965837+00:00
-- url     : https://prove2.me/submissions/f8567f86-6c28-449e-8c2a-198f78e199d9

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_half_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_inv_half_sq

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
variable {K : Type} [CommRing K] (R : Subring K)
variable {R}
variable (R) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (hMM : MM R) (hun : ∀ x : K, conj (ψ x) = ψ (-x))
    (hs : IsUnit ((m + 1 : ℕ) : K)) (t₁ t₂ z z' : Kˣ) (hN : modK R (z' : K) = modK R (z : K)) :
    germCoef R ψ m γ t₁ z * conj (germCoef R ψ m γ t₂ z') =
      γ (z * t₁) * conj (γ (z' * t₂)) *
        (((modK R ((m + 1 : ℕ) : K))⁻¹ * modK R (z : K) ^ (m ^ 2) : ℝ) : ℂ) *
        ψ (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
          ((m + 1 : ℕ) : K) * (z' : K) * ((t₂⁻¹ : Kˣ) : K)) := by
  have hS : 0 < modK R ((m + 1 : ℕ) : K) := by
    obtain ⟨u, hu⟩ := hs
    rw [← hu]
    exact (hMM u u).1
  have key : ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
      modK R (z : K) ^ ((m : ℝ) ^ 2 / 2) : ℝ) : ℂ) *
      ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) * modK R (z : K) ^ ((m : ℝ) ^ 2 / 2) : ℝ) : ℂ) =
      (((modK R ((m + 1 : ℕ) : K))⁻¹ * modK R (z : K) ^ (m ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← inv_half_sq _ hS, ← half_sq _ (hMM z z).1 m]
    ring
  unfold germCoef
  rw [map_mul (starRingEnd ℂ), map_mul (starRingEnd ℂ), Complex.conj_ofReal, hun, hN, sub_eq_add_neg, AddChar.map_add_eq_mul,
    ← key]
  ring
end Formalism.FourierDecayAlt.P.GermSumLattices
