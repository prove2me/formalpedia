-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.matrix_coefficient_integrable_double
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:02:54.494384+00:00
-- url     : https://prove2.me/submissions/2f7d0594-b7e7-4404-86a3-68c992cef031

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftingTheory
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormBallVolumes_gnLower
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormBallVolumes_gN_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormBallVolumes_ae_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormBallVolumes_one_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_matrix_coefficient_bound_by_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.NormBallVolumes
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.CCIntDouble := by
  intro hX k r Wp Wq _ _ _ _ _ _ D A hA
  by_cases hT : ∃ T : Wq →L[ℂ] Wp, T ≠ 0
  · obtain ⟨T, hT0⟩ := hT
    apply matrix_coefficient_bound_by_norm k r Wp Wq D A
    have hA1 : AB k r ≤ A / 2 := by linarith
    obtain ⟨Ξ, ⟨C, hC⟩, _⟩ := hX k r Wp Wq D (A / 2) hA1
    set F : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((gN g ^ (-(A / 2)) : ℝ) : ℂ) • T with hF
    have hm : AEStronglyMeasurable (fun g : Mt k r => F (Matrix.of g)) D.μG := by
      have h1 : Measurable fun g : Mt k r => ((gN (Matrix.of g) ^ (-(A / 2)) : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp ((gN_meas k r).pow_const _)
      exact h1.aestronglyMeasurable.smul_const T
    have hn : ∀ g : Mat k r, 0 < gN g → ‖F g‖ = gN g ^ (-(A / 2)) * ‖T‖ := by
      intro g hg
      simp only [hF, norm_smul, Complex.norm_real]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hg.le _)]
    have hb : ∀ g ∈ GV k r, gN g ^ (A / 2) * ‖F g‖ ≤ ‖T‖ := by
      intro g hg
      have hpos : 0 < gN g := lt_of_lt_of_le one_pos (gnLower k r g hg)
      rw [hn g hpos, ← mul_assoc, ← Real.rpow_add hpos]
      simp
    have hmain := hC F F ‖T‖ ‖T‖ hm hm hb hb 1 (one_mem k r) 1 (one_mem k r)
    have key : ∀ᵐ g ∂D.μG, ‖T‖ₑ * ‖T‖ₑ * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) =
        ‖F ((1 : Mat k r)⁻¹ * Matrix.of g * 1)‖ₑ * ‖F (Matrix.of g)‖ₑ := by
      filter_upwards [ae_mem D.haarG] with g hg
      have hpos : 0 < gN (Matrix.of g) := lt_of_lt_of_le one_pos (gnLower k r _ hg)
      have e1 : (1 : Mat k r)⁻¹ * Matrix.of g * 1 = Matrix.of g := by simp
      rw [e1, ← ofReal_norm (F (Matrix.of g)), hn _ hpos, ← ofReal_norm T,
        ← ENNReal.ofReal_mul (norm_nonneg T), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : gN (Matrix.of g) ^ (-A) = gN (Matrix.of g) ^ (-(A / 2)) * gN (Matrix.of g) ^ (-(A / 2)) := by
        rw [← Real.rpow_add hpos]; congr 1; ring
      rw [this]; ring
    have hfin : (∫⁻ g : Mt k r, ‖T‖ₑ * ‖T‖ₑ * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG) < ∞ := by
      rw [lintegral_congr_ae key]
      refine lt_of_le_of_lt hmain ?_
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top) ENNReal.coe_lt_top
    have hc : ‖T‖ₑ * ‖T‖ₑ ≠ ∞ := ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
    rw [lintegral_const_mul' _ _ hc] at hfin
    rcases ENNReal.mul_lt_top_iff.mp hfin with h | h | h
    · exact h.2
    · exfalso
      have : ‖T‖ₑ = 0 := by
        rcases mul_eq_zero.mp h with h | h <;> exact h
      exact hT0 (enorm_eq_zero.mp this)
    · rw [h]; exact ENNReal.zero_lt_top
  · simp only [not_exists, not_not] at hT
    intro F c _ _
    simp [hT]
end Formalism.FourierDecayAlt.P
