-- Prove2me | solution 1 for Formalism.REAL.sum_weighted_lie_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:25:51.970149+00:00
-- url     : https://prove2.me/submissions/8640b3f3-d5de-4095-bff3-532f9e9a0f3b

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport
import Theorems.Thm_Formalism_REAL_cutoff_profile_eq_one
import Theorems.Thm_Formalism_REAL_weight_profile_nonneg
import Theorems.Thm_Formalism_REAL_weight_profile_le_exp
import Theorems.Thm_Formalism_REAL_lie_derivative_weight_le
import Theorems.Thm_Formalism_REAL_amgm_mul_le
import Theorems.Thm_Formalism_REAL_integral_lie_derivative_weight_identity
import Theorems.Thm_Formalism_REAL_weight_mul_conj_eq
import Theorems.Thm_Formalism_REAL_integrable_weight_derivative_product
import Theorems.Thm_Formalism_REAL_integrable_weight_product
import Theorems.Thm_Formalism_REAL_integrable_weighted_norm_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
namespace Formalism.REAL
theorem _root_.solution (hl : HhLip) (hz : IntRdZero) {a : ℝ} (ha : 0 ≤ a) {R : ℝ} (hR : 1 ≤ R)
    {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u)
    (hu2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) (muG ε))
    (hT2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2)
      (muG ε)) :
    ∑ i, ∑ j, ∫ g : UJ ε, weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 ∂(muG ε) ≤
      ∑ i, ∑ j, ((2 * cutoffDerivBound + 2 * a) * lieDerivativeLogFrobeniusBound ε i j) ^ 2 *
          ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 ∂(muG ε) +
        ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 ∂(muG ε) +
        ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 ∂(muG ε) := by
  have hR0 : 0 < R := by linarith
  set Nu := ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 ∂(muG ε) with hNu
  set NT := ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 ∂(muG ε) with hNT
  set I : Fin n → Fin n → ℝ := fun i j =>
    ∫ g : UJ ε, weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 ∂(muG ε) with hIdef
  set K : Fin n → Fin n → ℝ := fun i j => (2 * cutoffDerivBound + 2 * a) * lieDerivativeLogFrobeniusBound ε i j with hK
  set C1 : Fin n → Fin n → ℂ := fun i j => ∫ g : UJ ε, Eab ε i j (radialWeight a R) (toM g) * u (toM g) *
      starRingEnd ℂ (Eab ε i j u (toM g)) ∂(muG ε) with hC1
  set C4 : ℂ := ∫ g : UJ ε, radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (signedCasimirDifference ε u (toM g))
    ∂(muG ε) with hC4

  have hI : ∀ i j, ((I i j : ℝ) : ℂ) = -C1 i j + ((sgn ε i j : ℝ) : ℂ) *
      ∫ g : UJ ε, radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g))
        ∂(muG ε) := by
    intro i j
    rw [← integral_lie_derivative_weight_identity hl hz a hR0 hu i j]
    simp only [hIdef]
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    exact (weight_mul_conj_eq a R _ _).symm

  have hsum : ∑ i, ∑ j, ((sgn ε i j : ℝ) : ℂ) *
      ∫ g : UJ ε, radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g))
        ∂(muG ε) = C4 := by
    have pw : ∀ g : UJ ε, radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (signedCasimirDifference ε u (toM g)) =
        ∑ i, ∑ j, ((sgn ε i j : ℝ) : ℂ) * (radialWeight a R (toM g) * u (toM g) *
          starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g))) := by
      intro g
      simp only [signedCasimirDifference, map_sum, map_mul, Complex.conj_ofReal]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hC4, integral_congr_ae (Eventually.of_forall pw), integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ =>
        (integrable_weight_product hl a hR0 hu (smooth_lie_derivative j i (smooth_lie_derivative i j hu))).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ =>
        (integrable_weight_product hl a hR0 hu (smooth_lie_derivative j i (smooth_lie_derivative i j hu))).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have hIi : ∀ i j, Integrable (fun g : UJ ε => weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2)
      (muG ε) := fun i j => integrable_weighted_norm_sq hl a hR0 (smooth_lie_derivative i j hu)
  have hC1b : ∀ i j, ‖C1 i j‖ ≤ I i j / 2 + K i j ^ 2 * Nu / 2 := by
    intro i j
    refine (norm_integral_le_integral_norm _).trans ?_
    have hb : ∀ g : UJ ε, ‖Eab ε i j (radialWeight a R) (toM g) * u (toM g) *
        starRingEnd ℂ (Eab ε i j u (toM g))‖ ≤
        weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 / 2 +
          K i j ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) / 2 := by
      intro g
      have h1 := lie_derivative_weight_le hl ha hR i j g.2
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have hχ := cutoff_profile_eq_one (hh (toM g) / R)
      have hE := Real.exp_pos (2 * a * hh (toM g))
      calc ‖Eab ε i j (radialWeight a R) (toM g)‖ * ‖u (toM g)‖ * ‖Eab ε i j u (toM g)‖
          ≤ radialCutoff R (hh (toM g)) * Real.exp (2 * a * hh (toM g)) * K i j * ‖u (toM g)‖ *
              ‖Eab ε i j u (toM g)‖ := by gcongr
        _ = (radialCutoff R (hh (toM g)) * ‖Eab ε i j u (toM g)‖) * (K i j * ‖u (toM g)‖) *
              Real.exp (2 * a * hh (toM g)) := by ring
        _ ≤ (radialCutoff R (hh (toM g)) * ‖Eab ε i j u (toM g)‖) ^ 2 * Real.exp (2 * a * hh (toM g)) / 2 +
              (K i j * ‖u (toM g)‖) ^ 2 * Real.exp (2 * a * hh (toM g)) / 2 :=
            amgm_mul_le _ _ _ hE.le
        _ = _ := by unfold weightProfileAlt; ring
    have hr1 : Integrable (fun g : UJ ε =>
        weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 / 2) (muG ε) :=
      Integrable.div_const (f := fun g : UJ ε =>
        weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2) (hIi i j) 2
    have hr2 : Integrable (fun g : UJ ε =>
        K i j ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) / 2) (muG ε) :=
      Integrable.div_const (f := fun g : UJ ε =>
        K i j ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2))
        (Integrable.const_mul (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2)
          hu2 _) 2
    have hr : Integrable (fun g : UJ ε =>
        weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 / 2 +
          K i j ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) / 2) (muG ε) :=
      Integrable.add (f := fun g : UJ ε => weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 / 2)
        (g := fun g : UJ ε => K i j ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) / 2)
        hr1 hr2
    calc ∫ g : UJ ε, ‖Eab ε i j (radialWeight a R) (toM g) * u (toM g) *
          starRingEnd ℂ (Eab ε i j u (toM g))‖ ∂(muG ε)
        ≤ ∫ g : UJ ε, (weightProfileAlt a R (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 / 2 +
          K i j ^ 2 * (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) / 2) ∂(muG ε) :=
          integral_mono (integrable_weight_derivative_product hl a hR0 hu i j).norm hr hb
      _ = I i j / 2 + K i j ^ 2 * Nu / 2 := by
          rw [integral_add hr1 hr2, integral_div, integral_div, integral_const_mul]
  have hC4b : ‖C4‖ ≤ Nu / 2 + NT / 2 := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hb : ∀ g : UJ ε, ‖radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (signedCasimirDifference ε u (toM g))‖ ≤
        Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 / 2 +
          Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 / 2 := by
      intro g
      rw [norm_mul, norm_mul, Complex.norm_conj]
      have hw : ‖radialWeight a R (toM g)‖ ≤ Real.exp (2 * a * hh (toM g)) := by
        unfold radialWeight
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_profile_nonneg _ _ _)]
        exact weight_profile_le_exp _ _ _
      have hE := Real.exp_pos (2 * a * hh (toM g))
      calc ‖radialWeight a R (toM g)‖ * ‖u (toM g)‖ * ‖signedCasimirDifference ε u (toM g)‖
          ≤ Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ * ‖signedCasimirDifference ε u (toM g)‖ := by gcongr
        _ = ‖u (toM g)‖ * ‖signedCasimirDifference ε u (toM g)‖ * Real.exp (2 * a * hh (toM g)) := by ring
        _ ≤ ‖u (toM g)‖ ^ 2 * Real.exp (2 * a * hh (toM g)) / 2 +
            ‖signedCasimirDifference ε u (toM g)‖ ^ 2 * Real.exp (2 * a * hh (toM g)) / 2 := amgm_mul_le _ _ _ hE.le
        _ = _ := by ring
    have hr1 : Integrable (fun g : UJ ε =>
        Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 / 2) (muG ε) :=
      Integrable.div_const (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) hu2 2
    have hr2 : Integrable (fun g : UJ ε =>
        Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 / 2) (muG ε) :=
      Integrable.div_const (f := fun g : UJ ε =>
        Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2) hT2 2
    have hr : Integrable (fun g : UJ ε =>
        Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 / 2 +
          Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 / 2) (muG ε) :=
      Integrable.add (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 / 2)
        (g := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 / 2) hr1 hr2
    calc ∫ g : UJ ε, ‖radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (signedCasimirDifference ε u (toM g))‖ ∂(muG ε)
        ≤ ∫ g : UJ ε, (Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 / 2 +
          Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 / 2) ∂(muG ε) :=
          integral_mono (integrable_weight_product hl a hR0 hu (smooth_signedCasimir hu)).norm hr hb
      _ = Nu / 2 + NT / 2 := by
          rw [integral_add hr1 hr2, integral_div, integral_div]
  have hc : ((∑ i, ∑ j, I i j : ℝ) : ℂ) = ∑ i, ∑ j, -C1 i j + C4 := by
    push_cast
    simp only [hI, Finset.sum_add_distrib, hsum]
  have hre : ∑ i, ∑ j, I i j = ∑ i, ∑ j, -(C1 i j).re + C4.re := by
    have := congrArg Complex.re hc
    simpa [Complex.re_sum] using this
  have h1 : ∑ i, ∑ j, -(C1 i j).re ≤ ∑ i, ∑ j, (I i j / 2 + K i j ^ 2 * Nu / 2) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (hC1b i j))
  have h2 : C4.re ≤ Nu / 2 + NT / 2 := (Complex.re_le_norm _).trans hC4b
  have h3 : ∑ i, ∑ j, (I i j / 2 + K i j ^ 2 * Nu / 2) =
      (∑ i, ∑ j, I i j) / 2 + (∑ i, ∑ j, K i j ^ 2 * Nu) / 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_div]
  linarith
end Formalism.REAL
