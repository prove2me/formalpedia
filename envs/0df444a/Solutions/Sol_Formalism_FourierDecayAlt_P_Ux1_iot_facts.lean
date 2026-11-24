-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.iot_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:17.086928+00:00
-- url     : https://prove2.me/submissions/1af3467a-b388-41e8-8370-fe14b21474ef

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {h : Mat k r} (hh : h ∈ GV k r) (hu : IsUnit (h + 1).det) :
    inLie k r (iot h) ∧ IsUnit (1 - iot h).det ∧ kap (iot h) = h := by
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  set D := h + 1 with hD
  set C := h - 1 with hC
  have hDD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ hu
  have hDD' : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hZD : iot h * D = C := by
    unfold iot; rw [Matrix.mul_assoc, hDD, Matrix.mul_one]

  have h1Z : 1 - iot h = (2 : ℂ) • D⁻¹ := by
    have : (1 - iot h) * D = (2 : ℂ) • (1 : Mat k r) := by
      rw [Matrix.sub_mul, Matrix.one_mul, hZD, hD, hC]
      rw [two_smul]; abel
    calc 1 - iot h = (1 - iot h) * D * D⁻¹ := by rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
      _ = (2 : ℂ) • D⁻¹ := by rw [this, Matrix.smul_mul, Matrix.one_mul]
  have hu1 : IsUnit (1 - iot h).det := by
    rw [h1Z, Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 two_ne_zero)).mul (Matrix.isUnit_nonsing_inv_det _ hu)
  refine ⟨?_, hu1, ?_⟩
  ·
    have hDu : IsUnit (Dᴴ).det := by rw [det_conjTranspose]; exact hu.star
    have e1 : Cᴴ * Hpk k r * D = hᴴ * Hpk k r - Hpk k r * h := by
      rw [hC, hD, conjTranspose_sub, conjTranspose_one]
      calc (hᴴ - 1) * Hpk k r * (h + 1) = hᴴ * Hpk k r * h + hᴴ * Hpk k r - Hpk k r * h - Hpk k r := by
            noncomm_ring
        _ = hᴴ * Hpk k r - Hpk k r * h := by rw [hh']; abel
    have e2 : Dᴴ * Hpk k r * C = -(hᴴ * Hpk k r - Hpk k r * h) := by
      rw [hC, hD, conjTranspose_add, conjTranspose_one]
      calc (hᴴ + 1) * Hpk k r * (h - 1) = hᴴ * Hpk k r * h - hᴴ * Hpk k r + Hpk k r * h - Hpk k r := by
            noncomm_ring
        _ = -(hᴴ * Hpk k r - Hpk k r * h) := by rw [hh']; abel
    have e3 : Dᴴ * ((iot h)ᴴ * Hpk k r + Hpk k r * iot h) * D = 0 := by
      have : Dᴴ * ((iot h)ᴴ * Hpk k r + Hpk k r * iot h) * D
          = (iot h * D)ᴴ * Hpk k r * D + Dᴴ * Hpk k r * (iot h * D) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      rw [this, hZD, e1, e2, add_neg_cancel]
    have hDH : (Dᴴ)⁻¹ * Dᴴ = 1 := Matrix.nonsing_inv_mul _ hDu
    show (iot h)ᴴ * Hpk k r + Hpk k r * iot h = 0
    calc (iot h)ᴴ * Hpk k r + Hpk k r * iot h
        = (Dᴴ)⁻¹ * (Dᴴ * ((iot h)ᴴ * Hpk k r + Hpk k r * iot h) * D) * D⁻¹ := by
          simp only [← Matrix.mul_assoc, hDH, Matrix.one_mul]
          rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
      _ = 0 := by rw [e3, Matrix.mul_zero, Matrix.zero_mul]
  ·
    have hp : (1 + iot h) * D = h * ((1 - iot h) * D) := by
      rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, hZD, hD, hC]; noncomm_ring
    have hq : 1 + iot h = h * (1 - iot h) := by
      calc 1 + iot h = (1 + iot h) * D * D⁻¹ := by rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
        _ = h * (1 - iot h) := by rw [hp, ← Matrix.mul_assoc, Matrix.mul_assoc _ D, hDD', Matrix.mul_one]
    unfold kap
    rw [hq, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.Ux1
