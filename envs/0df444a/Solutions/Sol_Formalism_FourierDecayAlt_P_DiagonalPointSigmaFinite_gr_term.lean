-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.gr_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:03.036855+00:00
-- url     : https://prove2.me/submissions/e065ceec-cd23-473b-a751-e3af516bbdf8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution (m : ℕ) (Cz Yz Lz OLz : V) (ψ : ℂ) (hψ : ‖ψ‖ = 1) (τ ζ a3 a4 : ℝ) (hτ : 0 < τ) (hζ : 0 < ζ)
    (h3 : ‖Cz - (ψ * ((τ ^ (m + 1) * ζ ^ (m + 1) / ((m : ℝ) + 2) : ℝ) : ℂ)) • Yz‖ ≤ a3 * τ ^ (m + 2))
    (h4 : ‖Yz - (((ζ ^ (2 * (m + 1)))⁻¹ : ℝ) : ℂ) • Lz‖ ≤ a4 * τ)
    (hL : Lz = ((ζ ^ ((m + 1 + 1) * (m + 1)) : ℝ) : ℂ) • OLz) :
    ‖(((τ ^ (m + 1))⁻¹ : ℝ) : ℂ) • Cz -
        ((m : ℂ) + 2)⁻¹ • ((((ζ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * 1 * ψ) • OLz)‖ ≤ (a3 + ζ ^ (m + 1) * a4) * τ := by
  have hs : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hsC : ((m : ℂ) + 2) ≠ 0 := by
    have : (((m : ℝ) + 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    simpa using this
  have hτC : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ.ne'
  have hζC : (ζ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hζ.ne'
  have e1 : (((τ ^ (m + 1))⁻¹ : ℝ) : ℂ) * (ψ * ((τ ^ (m + 1) * ζ ^ (m + 1) / ((m : ℝ) + 2) : ℝ) : ℂ)) =
      ψ * ((ζ ^ (m + 1) / ((m : ℝ) + 2) : ℝ) : ℂ) := by
    push_cast
    field_simp
  have e2 : ψ * ((ζ ^ (m + 1) / ((m : ℝ) + 2) : ℝ) : ℂ) * (((ζ ^ (2 * (m + 1)))⁻¹ : ℝ) : ℂ) *
      ((ζ ^ ((m + 1 + 1) * (m + 1)) : ℝ) : ℂ) = ((m : ℂ) + 2)⁻¹ * (((ζ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * 1 * ψ) := by
    push_cast
    field_simp
    ring
  have key : (((τ ^ (m + 1))⁻¹ : ℝ) : ℂ) • Cz -
        ((m : ℂ) + 2)⁻¹ • ((((ζ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * 1 * ψ) • OLz) =
      (((τ ^ (m + 1))⁻¹ : ℝ) : ℂ) • (Cz - (ψ * ((τ ^ (m + 1) * ζ ^ (m + 1) / ((m : ℝ) + 2) : ℝ) : ℂ)) • Yz) +
      (ψ * ((ζ ^ (m + 1) / ((m : ℝ) + 2) : ℝ) : ℂ)) • (Yz - (((ζ ^ (2 * (m + 1)))⁻¹ : ℝ) : ℂ) • Lz) := by
    rw [hL, smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, e1, e2]
    abel
  rw [key]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_mul, hψ, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have b1 : (τ ^ (m + 1))⁻¹ * ‖Cz - (ψ * ((τ ^ (m + 1) * ζ ^ (m + 1) / ((m : ℝ) + 2) : ℝ) : ℂ)) • Yz‖ ≤ a3 * τ := by
    calc _ ≤ (τ ^ (m + 1))⁻¹ * (a3 * τ ^ (m + 2)) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = a3 * τ := by field_simp; ring
  have h4' : 0 ≤ a4 * τ := (norm_nonneg _).trans h4
  have b2 : ζ ^ (m + 1) / ((m : ℝ) + 2) * ‖Yz - (((ζ ^ (2 * (m + 1)))⁻¹ : ℝ) : ℂ) • Lz‖ ≤ ζ ^ (m + 1) * (a4 * τ) := by
    calc _ ≤ ζ ^ (m + 1) / ((m : ℝ) + 2) * (a4 * τ) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ ζ ^ (m + 1) * (a4 * τ) := by
        apply mul_le_mul_of_nonneg_right _ h4'
        apply div_le_self (by positivity)
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
  calc _ ≤ a3 * τ + ζ ^ (m + 1) * (a4 * τ) := add_le_add b1 b2
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
