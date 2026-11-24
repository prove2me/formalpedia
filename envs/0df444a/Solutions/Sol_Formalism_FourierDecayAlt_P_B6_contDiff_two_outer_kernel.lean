-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.contDiff_two_outer_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:38.476428+00:00
-- url     : https://prove2.me/submissions/1d3bb685-ac3e-4ac8-bd04-a88fe28814c7

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gam_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_nonpositive_not_in_interval
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regularised_product_second_derivative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2)
    (ρ : ℝ) (q : ℕ → ℕ → ℝ → ℝ → ℂ)
    (hx : ∀ m < 2, ∀ l ≤ 2, ∀ x > 0, ∀ y > 0,
      HasDerivAt (fun x' => q m l x' y) (((-(ρ / x) : ℝ) : ℂ) * q (m + 1) l x y) x)
    (hc : ∀ m ≤ 2, ∀ l ≤ 2, ContinuousOn (fun t : ℝ × ℝ => q m l t.1 t.2) Quad) (y : ℝ) :
    ContDiff ℝ 2 (fun x => regularised_kernel_product ρ W q x y) ∧
      ∀ x, regularised_kernel_product ρ W q x y - iteratedDeriv 2 (fun x' => regularised_kernel_product ρ W q x' y) x =
        ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3, ((gam ρ W m x * gam ρ W l y : ℝ) : ℂ) * q m l x y := by
  by_cases hy0 : 0 < y
  · have cq : ∀ l ≤ 2, ContinuousOn (fun x => q 2 l x y) (Set.Ioi 0) := fun l hl =>
      (hc 2 le_rfl l hl).comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx0 => ⟨hx0, hy0⟩)
    have hd : ∀ m < 2, ∀ t, 0 < t → HasDerivAt
        (fun x => (gam ρ W 0 y : ℂ) * q m 0 x y + (gam ρ W 1 y : ℂ) * q m 1 x y + (gam ρ W 2 y : ℂ) * q m 2 x y)
        (((-(ρ / t) : ℝ) : ℂ) * ((gam ρ W 0 y : ℂ) * q (m + 1) 0 t y + (gam ρ W 1 y : ℂ) * q (m + 1) 1 t y +
          (gam ρ W 2 y : ℂ) * q (m + 1) 2 t y)) t := fun m hm t ht => by
      refine ((((hx m hm 0 (by norm_num) t ht y hy0).const_mul (gam ρ W 0 y : ℂ)).add
        ((hx m hm 1 (by norm_num) t ht y hy0).const_mul (gam ρ W 1 y : ℂ))).add
        ((hx m hm 2 le_rfl t ht y hy0).const_mul (gam ρ W 2 y : ℂ))).congr_deriv ?_
      ring
    obtain ⟨cd, fm⟩ := regularised_product_second_derivative hW hWs ρ (hd 0 (by norm_num)) (hd 1 (by norm_num))
      (((continuousOn_const.mul (cq 0 (by norm_num))).add (continuousOn_const.mul (cq 1 (by norm_num)))).add
        (continuousOn_const.mul (cq 2 le_rfl)))
    refine ⟨cd, fun x => ?_⟩
    have := fm x
    unfold regularised_kernel_product
    rw [this]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast; ring
  · have g0 : ∀ l, gam ρ W l y = 0 := fun l => gam_zero hWs ρ l (nonpositive_not_in_interval (not_lt.1 hy0))
    have e : (fun x => regularised_kernel_product ρ W q x y) = fun _ => 0 := by
      funext x; simp [regularised_kernel_product, g0]
    refine ⟨by rw [e]; exact contDiff_const, fun x => ?_⟩
    rw [e]
    simp [regularised_kernel_product, g0]
end Formalism.FourierDecayAlt.P.B6
