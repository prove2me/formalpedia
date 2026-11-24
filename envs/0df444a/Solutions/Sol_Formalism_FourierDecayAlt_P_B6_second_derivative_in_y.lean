-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.second_derivative_in_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:40.123125+00:00
-- url     : https://prove2.me/submissions/40e51af6-ed70-4e65-b647-809f571db587

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_zero_outside
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
    (hy : ∀ l < 2, ∀ x > 0, ∀ y > 0,
      HasDerivAt (fun y' => q 0 l x y') (((-(ρ / y) : ℝ) : ℂ) * q 0 (l + 1) x y) y)
    (hc : ∀ m ≤ 2, ∀ l ≤ 2, ContinuousOn (fun t : ℝ × ℝ => q m l t.1 t.2) Quad)
    (h : ℝ → ℝ → ℂ) (hh : ∀ x y, h x y = ((W x * W y : ℝ) : ℂ) * q 0 0 x y) (x : ℝ) :
    ContDiff ℝ 2 (fun y => h x y) ∧
      ∀ y, h x y - iteratedDeriv 2 (fun y' => h x y') y = regularised_kernel_product ρ W q x y := by
  have e : (fun y => h x y) = fun y => (W x : ℂ) * ((W y : ℂ) * q 0 0 x y) := by
    funext y; rw [hh]; push_cast; ring
  have e' : ∀ y, h x y = (W x : ℂ) * ((W y : ℂ) * q 0 0 x y) := fun y => congrFun e y
  by_cases hx0 : 0 < x
  · have cq : ContinuousOn (q 0 2 x) (Set.Ioi 0) :=
      (hc 0 (by norm_num) 2 le_rfl).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun y hy0 => ⟨hx0, hy0⟩)
    obtain ⟨cd, fm⟩ := regularised_product_second_derivative hW hWs ρ (q0 := q 0 0 x) (q1 := q 0 1 x) (q2 := q 0 2 x)
      (fun t ht => hy 0 (by norm_num) x hx0 t ht) (fun t ht => hy 1 (by norm_num) x hx0 t ht) cq
    refine ⟨by rw [e]; exact contDiff_const.mul cd, fun y => ?_⟩
    rw [e, e' y, iteratedDeriv_const_mul_field, ← mul_sub, fm y]
    rfl
  · have hW0 : W x = 0 := cutoff_zero_outside hWs (nonpositive_not_in_interval (not_lt.1 hx0))
    refine ⟨?_, fun y => ?_⟩
    · rw [e, hW0]; simp only [Complex.ofReal_zero, zero_mul]; exact contDiff_const
    · rw [e, e' y, iteratedDeriv_const_mul_field, hW0]; simp [regularised_kernel_product, hW0]
end Formalism.FourierDecayAlt.P.B6
