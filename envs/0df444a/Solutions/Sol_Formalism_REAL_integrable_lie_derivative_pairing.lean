-- Prove2me | solution 1 for Formalism.REAL.integrable_lie_derivative_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:00:43.372147+00:00
-- url     : https://prove2.me/submissions/6a1b294c-d0b3-4fa8-bcdf-cb3c19616aa4

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
import Theorems.Thm_Formalism_REAL_smooth_on_group_conj
import Theorems.Thm_Formalism_REAL_lie_derivative_mul
import Theorems.Thm_Formalism_REAL_lie_derivative_conj
import Theorems.Thm_Formalism_REAL_lie_derivative_bound_nonneg
import Theorems.Thm_Formalism_REAL_lie_derivative_log_frobenius_comp_le
import Theorems.Thm_Formalism_REAL_vanishing_outside_lie_derivative
import Theorems.Thm_Formalism_REAL_vanishing_outside_mul_left
import Theorems.Thm_Formalism_REAL_integrable_of_vanishing_outside
import Theorems.Thm_Formalism_REAL_integral_lie_derivative_eq_zero
import Theorems.Thm_Formalism_REAL_contDiff_radialCutoff
import Theorems.Thm_Formalism_REAL_abs_deriv_cutoff_le
import Theorems.Thm_Formalism_REAL_integrable_mul_conj_of_weighted
import Theorems.Thm_Formalism_REAL_smooth_cutoff
import Theorems.Thm_Formalism_REAL_cutoff_vanishing_outside
import Theorems.Thm_Formalism_REAL_tendsto_integral_cutoff

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
theorem _root_.solution (hl : HhLip) (hz : IntRdZero) {a : ℝ} (ha : 0 ≤ a)
    {u u' : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u) (hu' : SmoothOnG ε u')
    (hu2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) (muG ε))
    (hu2' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u' (toM g)‖ ^ 2) (muG ε))
    (i j : Fin n)
    (hv2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2)
      (muG ε))
    (hv2' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eab ε j i u' (toM g)‖ ^ 2)
      (muG ε)) :
    ∫ g : UJ ε, Eab ε i j u (toM g) * starRingEnd ℂ (u' (toM g)) ∂(muG ε) =
      ((sgn ε i j : ℝ) : ℂ) * ∫ g : UJ ε, u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g)) ∂(muG ε) := by
  have hv := smooth_lie_derivative i j hu
  have hv' := smooth_lie_derivative j i hu'
  have P1 := integrable_mul_conj_of_weighted ha hv hu' hv2 hu2'
  have P2 := integrable_mul_conj_of_weighted ha hu hv' hu2 hv2'
  have P0 := integrable_mul_conj_of_weighted ha hu hu' hu2 hu2'
  set s : ℂ := ((sgn ε i j : ℝ) : ℂ) with hs
  set A : ℕ → ℂ := fun N => ∫ g : UJ ε, radialCutoffFunction ((N : ℝ) + 1) (toM g) *
    (Eab ε i j u (toM g) * starRingEnd ℂ (u' (toM g))) ∂(muG ε) with hA
  set Bq : ℕ → ℂ := fun N => ∫ g : UJ ε, radialCutoffFunction ((N : ℝ) + 1) (toM g) *
    (u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g))) ∂(muG ε) with hBq
  set C : ℕ → ℂ := fun N => ∫ g : UJ ε, Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) (toM g) * u (toM g) *
    starRingEnd ℂ (u' (toM g)) ∂(muG ε) with hC
  have hrel : ∀ N, A N = s * Bq N - C N := by
    intro N
    have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have csm := smooth_cutoff (ε := ε) hl ((N : ℝ) + 1)
    have cv := cutoff_vanishing_outside (ε := ε) hR
    have hφs : SmoothOnG ε (fun x => (radialCutoffFunction ((N : ℝ) + 1) x * u x) * starRingEnd ℂ (u' x)) :=
      smooth_on_group_mul (smooth_on_group_mul csm hu) (smooth_on_group_conj hu')
    have hφv : VanishesOutsideBall ε (Real.exp (2 * ((N : ℝ) + 1)))
        (fun x => (radialCutoffFunction ((N : ℝ) + 1) x * u x) * starRingEnd ℂ (u' x)) :=
      vanishing_outside_mul_left _ (vanishing_outside_mul_left _ cv)
    have h0 := integral_lie_derivative_eq_zero hz hφs hφv i j
    have key : ∀ g : UJ ε, Eab ε i j (fun x => (radialCutoffFunction ((N : ℝ) + 1) x * u x) * starRingEnd ℂ (u' x))
        (toM g) = Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) (toM g) * u (toM g) * starRingEnd ℂ (u' (toM g)) +
          radialCutoffFunction ((N : ℝ) + 1) (toM g) * (Eab ε i j u (toM g) * starRingEnd ℂ (u' (toM g))) +
          (-s) * (radialCutoffFunction ((N : ℝ) + 1) (toM g) * (u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g)))) := by
      intro g
      rw [lie_derivative_mul i j (smooth_on_group_mul csm hu) (smooth_on_group_conj hu') g.2, lie_derivative_mul i j csm hu g.2,
        lie_derivative_conj i j hu' g.2]
      ring
    have i1 : Integrable (fun g : UJ ε => Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) (toM g) * u (toM g) *
        starRingEnd ℂ (u' (toM g))) (muG ε) :=
      integrable_of_vanishing_outside (f := fun x => Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) x * u x * starRingEnd ℂ (u' x))
        (smooth_on_group_mul (smooth_on_group_mul (smooth_lie_derivative i j csm) hu) (smooth_on_group_conj hu'))
        (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ (vanishing_outside_lie_derivative i j cv)))
    have i2 : Integrable (fun g : UJ ε => radialCutoffFunction ((N : ℝ) + 1) (toM g) *
        (Eab ε i j u (toM g) * starRingEnd ℂ (u' (toM g)))) (muG ε) :=
      integrable_of_vanishing_outside (f := fun x => radialCutoffFunction ((N : ℝ) + 1) x * (Eab ε i j u x * starRingEnd ℂ (u' x)))
        (smooth_on_group_mul csm (smooth_on_group_mul hv (smooth_on_group_conj hu'))) (vanishing_outside_mul_left _ cv)
    have i3 : Integrable (fun g : UJ ε => radialCutoffFunction ((N : ℝ) + 1) (toM g) *
        (u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g)))) (muG ε) :=
      integrable_of_vanishing_outside (f := fun x => radialCutoffFunction ((N : ℝ) + 1) x * (u x * starRingEnd ℂ (Eab ε j i u' x)))
        (smooth_on_group_mul csm (smooth_on_group_mul hu (smooth_on_group_conj hv'))) (vanishing_outside_mul_left _ cv)
    rw [integral_congr_ae (Eventually.of_forall key)] at h0
    have e1 := integral_add (i1.add i2) (i3.const_mul (-s))
    simp only [Pi.add_apply] at e1
    rw [integral_add i1 i2, integral_const_mul] at e1
    rw [e1] at h0
    simp only [hA, hBq, hC]
    linear_combination h0
  have hCt : Tendsto C atTop (𝓝 0) := by
    set P := ∫ g : UJ ε, ‖u (toM g) * starRingEnd ℂ (u' (toM g))‖ ∂(muG ε)
    have hb : ∀ N : ℕ, ‖C N‖ ≤ cutoffDerivBound * lieDerivativeLogFrobeniusBound ε i j * P * (1 / ((N : ℝ) + 1)) := by
      intro N
      have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      refine (norm_integral_le_integral_norm _).trans ?_
      have hpt : ∀ g : UJ ε, ‖Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) (toM g) * u (toM g) *
          starRingEnd ℂ (u' (toM g))‖ ≤ (cutoffDerivBound * lieDerivativeLogFrobeniusBound ε i j * (1 / ((N : ℝ) + 1))) *
            ‖u (toM g) * starRingEnd ℂ (u' (toM g))‖ := by
        intro g
        have h1 : ‖Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) (toM g)‖ ≤
            cutoffDerivBound * lieDerivativeLogFrobeniusBound ε i j * (1 / ((N : ℝ) + 1)) := by
          have := lie_derivative_log_frobenius_comp_le (ε := ε) hl (radialCutoff ((N : ℝ) + 1)) (contDiff_radialCutoff _) i j g.2
          refine this.trans ?_
          have h2 := abs_deriv_cutoff_le hR (hh (toM g))
          have hL := lie_derivative_bound_nonneg ε i j
          calc |deriv (radialCutoff ((N : ℝ) + 1)) (hh (toM g))| * lieDerivativeLogFrobeniusBound ε i j ≤
              cutoffDerivBound / ((N : ℝ) + 1) * lieDerivativeLogFrobeniusBound ε i j := by gcongr
            _ = _ := by ring
        rw [mul_assoc, norm_mul]
        gcongr
      have hi : Integrable (fun g : UJ ε => (cutoffDerivBound * lieDerivativeLogFrobeniusBound ε i j * (1 / ((N : ℝ) + 1))) *
          ‖u (toM g) * starRingEnd ℂ (u' (toM g))‖) (muG ε) :=
        Integrable.const_mul (f := fun g : UJ ε => ‖u (toM g) * starRingEnd ℂ (u' (toM g))‖)
          P0.norm _
      have i1 : Integrable (fun g : UJ ε => Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) (toM g) * u (toM g) *
          starRingEnd ℂ (u' (toM g))) (muG ε) :=
        integrable_of_vanishing_outside (f := fun x => Eab ε i j (radialCutoffFunction ((N : ℝ) + 1)) x * u x * starRingEnd ℂ (u' x))
          (smooth_on_group_mul (smooth_on_group_mul (smooth_lie_derivative i j (smooth_cutoff hl _)) hu) (smooth_on_group_conj hu'))
          (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ (vanishing_outside_lie_derivative i j (cutoff_vanishing_outside hR))))
      refine (integral_mono i1.norm hi hpt).trans ?_
      rw [integral_const_mul]
      ring_nf; rfl
    have ht : Tendsto (fun N : ℕ => cutoffDerivBound * lieDerivativeLogFrobeniusBound ε i j * P * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (cutoffDerivBound * lieDerivativeLogFrobeniusBound ε i j * P)
      simpa using this
    exact squeeze_zero_norm hb ht
  have hAt : Tendsto A atTop (𝓝 (∫ g : UJ ε, Eab ε i j u (toM g) * starRingEnd ℂ (u' (toM g))
      ∂(muG ε))) := tendsto_integral_cutoff P1
  have hBt : Tendsto Bq atTop (𝓝 (∫ g : UJ ε, u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g))
      ∂(muG ε))) := tendsto_integral_cutoff P2
  have hAt2 : Tendsto A atTop (𝓝 (s * (∫ g : UJ ε, u (toM g) * starRingEnd ℂ (Eab ε j i u' (toM g))
      ∂(muG ε)) - 0)) := by
    have := (hBt.const_mul s).sub hCt
    refine this.congr' (Eventually.of_forall fun N => ?_)
    exact (hrel N).symm
  rw [sub_zero] at hAt2
  exact tendsto_nhds_unique hAt hAt2
end Formalism.REAL
