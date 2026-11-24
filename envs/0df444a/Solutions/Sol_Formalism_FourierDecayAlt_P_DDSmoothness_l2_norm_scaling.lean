-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.l2_norm_scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:50:46.739867+00:00
-- url     : https://prove2.me/submissions/d23ca485-2378-45a8-ae91-32591c9b1376

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_inner_self_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
namespace Formalism.FourierDecayAlt.P.DDSmoothness
theorem _root_.solution {νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (T F : Mx k r → Wp) (a : Wp) (U D : ℝ) (hU : 0 ≤ U)
    (hN : PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq T =
      ENNReal.ofReal (U * (⟪a, ⟪a, a⟫_ℂ • a⟫_ℂ).re / D))
    (hae : ∀ᵐ x ∂νq, T (Matrix.of x) = ⟪a, a⟫_ℂ • F (Matrix.of x)) :
    ENNReal.ofReal (‖a‖ ^ 2) * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F =
      ENNReal.ofReal (U * ‖a‖ ^ 2 / D) := by
  have hinner : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := inner_self_cast a
  have hnq : ‖⟪a, a⟫_ℂ‖ = ‖a‖ ^ 2 := by
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc : (‖⟪a, a⟫_ℂ‖₊ : ENNReal) = ENNReal.ofReal (‖a‖ ^ 2) := by
    rw [← hnq]
    exact (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).symm
  have hT : PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq T =
      ENNReal.ofReal (‖a‖ ^ 2) ^ 2 * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [← lintegral_const_mul' (ENNReal.ofReal (‖a‖ ^ 2) ^ 2) _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    refine lintegral_congr_ae (hae.mono fun x hx => ?_)
    dsimp only
    rw [hx, nnnorm_smul, ENNReal.coe_mul, mul_pow, hc]
  have hre : (⟪a, ⟪a, a⟫_ℂ • a⟫_ℂ).re = ‖a‖ ^ 4 := by
    rw [inner_smul_right, hinner, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hT, hre] at hN
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hp : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
  have key : ENNReal.ofReal (‖a‖ ^ 2) * (ENNReal.ofReal (‖a‖ ^ 2) * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F) =
      ENNReal.ofReal (‖a‖ ^ 2) * ENNReal.ofReal (U * ‖a‖ ^ 2 / D) := by
    rw [← mul_assoc, ← pow_two, hN, ← ENNReal.ofReal_mul hp.le]
    congr 1
    ring
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp key
end Formalism.FourierDecayAlt.P.DDSmoothness
