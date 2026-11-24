-- Prove2me | solution 1 for Formalism.REAL.integral_lie_derivative_weight_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:59:04.564832+00:00
-- url     : https://prove2.me/submissions/3f64cb25-78e6-4da9-92eb-bda43ff411de

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
import Theorems.Thm_Formalism_REAL_vanishing_outside_lie_derivative
import Theorems.Thm_Formalism_REAL_vanishing_outside_mul_left
import Theorems.Thm_Formalism_REAL_integrable_of_vanishing_outside
import Theorems.Thm_Formalism_REAL_integral_lie_derivative_eq_zero
import Theorems.Thm_Formalism_REAL_smooth_weight
import Theorems.Thm_Formalism_REAL_weight_vanishing_outside

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
theorem _root_.solution (hl : HhLip) (hz : IntRdZero) (a : ℝ) {R : ℝ} (hR : 0 < R)
    {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u) (i j : Fin n) :
    ∫ g : UJ ε, radialWeight a R (toM g) * Eab ε i j u (toM g) * starRingEnd ℂ (Eab ε i j u (toM g))
        ∂(muG ε) =
      -∫ g : UJ ε, Eab ε i j (radialWeight a R) (toM g) * u (toM g) * starRingEnd ℂ (Eab ε i j u (toM g))
        ∂(muG ε) +
      ((sgn ε i j : ℝ) : ℂ) * ∫ g : UJ ε, radialWeight a R (toM g) * u (toM g) *
        starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g)) ∂(muG ε) := by
  have wsm := smooth_weight (ε := ε) hl a R
  have wv := weight_vanishing_outside (ε := ε) a hR
  have hv := smooth_lie_derivative i j hu
  have hφs : SmoothOnG ε (fun x => (radialWeight a R x * u x) * starRingEnd ℂ (Eab ε i j u x)) :=
    smooth_on_group_mul (smooth_on_group_mul wsm hu) (smooth_on_group_conj hv)
  have hφv : VanishesOutsideBall ε (Real.exp (2 * R))
      (fun x => (radialWeight a R x * u x) * starRingEnd ℂ (Eab ε i j u x)) :=
    vanishing_outside_mul_left _ (vanishing_outside_mul_left _ wv)
  have h0 := integral_lie_derivative_eq_zero hz hφs hφv i j
  have key : ∀ g : UJ ε, Eab ε i j (fun x => (radialWeight a R x * u x) * starRingEnd ℂ (Eab ε i j u x))
      (toM g) = Eab ε i j (radialWeight a R) (toM g) * u (toM g) * starRingEnd ℂ (Eab ε i j u (toM g)) +
        radialWeight a R (toM g) * Eab ε i j u (toM g) * starRingEnd ℂ (Eab ε i j u (toM g)) +
        (-((sgn ε i j : ℝ) : ℂ)) * (radialWeight a R (toM g) * u (toM g) *
          starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g))) := by
    intro g
    rw [lie_derivative_mul i j (smooth_on_group_mul wsm hu) (smooth_on_group_conj hv) g.2, lie_derivative_mul i j wsm hu g.2,
      lie_derivative_conj i j hv g.2]
    ring
  have i1 : Integrable (fun g : UJ ε => Eab ε i j (radialWeight a R) (toM g) * u (toM g) *
      starRingEnd ℂ (Eab ε i j u (toM g))) (muG ε) :=
    integrable_of_vanishing_outside (f := fun x => Eab ε i j (radialWeight a R) x * u x * starRingEnd ℂ (Eab ε i j u x))
      (smooth_on_group_mul (smooth_on_group_mul (smooth_lie_derivative i j wsm) hu) (smooth_on_group_conj hv))
      (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ (vanishing_outside_lie_derivative i j wv)))
  have i2 : Integrable (fun g : UJ ε => radialWeight a R (toM g) * Eab ε i j u (toM g) *
      starRingEnd ℂ (Eab ε i j u (toM g))) (muG ε) :=
    integrable_of_vanishing_outside (f := fun x => radialWeight a R x * Eab ε i j u x * starRingEnd ℂ (Eab ε i j u x))
      (smooth_on_group_mul (smooth_on_group_mul wsm hv) (smooth_on_group_conj hv))
      (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ wv))
  have i3 : Integrable (fun g : UJ ε => radialWeight a R (toM g) * u (toM g) *
      starRingEnd ℂ (Eab ε j i (Eab ε i j u) (toM g))) (muG ε) :=
    integrable_of_vanishing_outside (f := fun x => radialWeight a R x * u x * starRingEnd ℂ (Eab ε j i (Eab ε i j u) x))
      (smooth_on_group_mul (smooth_on_group_mul wsm hu) (smooth_on_group_conj (smooth_lie_derivative j i hv)))
      (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ wv))
  rw [integral_congr_ae (Eventually.of_forall key)] at h0
  have e1 := integral_add (i1.add i2) (i3.const_mul (-((sgn ε i j : ℝ) : ℂ)))
  simp only [Pi.add_apply] at e1
  rw [integral_add i1 i2, integral_const_mul] at e1
  rw [e1] at h0
  linear_combination h0
end Formalism.REAL
