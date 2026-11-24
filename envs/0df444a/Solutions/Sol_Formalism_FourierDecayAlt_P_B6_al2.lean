-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.al2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:33:50.472327+00:00
-- url     : https://prove2.me/submissions/81097d2e-d42b-47b8-9a30-8aa1da505025

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_zero_outside
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gam_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gam_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_product_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuous_exp_I_linear_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_fourier_slice_in_x
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_integral_slice_second_variable_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_second_derivative_in_y
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_contDiff_two_outer_kernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_integration_by_parts_regularised


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
    (hx : ∀ m < 2, ∀ l ≤ 2, ∀ x > 0, ∀ y > 0,
      HasDerivAt (fun x' => q m l x' y) (((-(ρ / x) : ℝ) : ℂ) * q (m + 1) l x y) x)
    (hc : ∀ m ≤ 2, ∀ l ≤ 2, ContinuousOn (fun t : ℝ × ℝ => q m l t.1 t.2) Quad)
    (h : ℝ → ℝ → ℂ) (hh : ∀ x y, h x y = ((W x * W y : ℝ) : ℂ) * q 0 0 x y) :
    (∀ x y, oneMinusDD h x y = ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
      ((gam ρ W m x * gam ρ W l y : ℝ) : ℂ) * q m l x y) ∧
    (∀ x, ContDiff ℝ 2 (fun y => h x y)) ∧
    (∀ y, ContDiff ℝ 2 (fun x => h x y - iteratedDeriv 2 (fun y' => h x y') y)) ∧
    (∀ x₁ x₂ : ℝ, (∫ t : ℝ × ℝ, oneMinusDD h t.1 t.2 *
        Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) =
      (((1 + x₁ ^ 2) * (1 + x₂ ^ 2) : ℝ) : ℂ) *
        ∫ t : ℝ × ℝ, h t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ))) := by
  have IN := second_derivative_in_y hW hWs ρ q hy hc h hh
  have OUT := contDiff_two_outer_kernel hW hWs ρ q hx hc
  have ek : ∀ y, (fun x => h x y - iteratedDeriv 2 (fun y' => h x y') y) = fun x => regularised_kernel_product ρ W q x y :=
    fun y => funext fun x => (IN x).2 y
  have om_eq : ∀ x y, oneMinusDD h x y =
      regularised_kernel_product ρ W q x y - iteratedDeriv 2 (fun x' => regularised_kernel_product ρ W q x' y) x := fun x y => by
    unfold oneMinusDD
    rw [ek y, (IN x).2 y]
  have form : ∀ x y, oneMinusDD h x y = ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
      ((gam ρ W m x * gam ρ W l y : ℝ) : ℂ) * q m l x y := fun x y => by
    rw [om_eq]; exact (OUT y).2 x
  refine ⟨form, fun x => (IN x).1, fun y => by rw [ek y]; exact (OUT y).1, fun x₁ x₂ => ?_⟩
  have cW : Continuous W := hW.continuous
  have zW : ∀ t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → W t = 0 := fun t ht => cutoff_zero_outside hWs ht
  have cg := gam_continuous hW hWs ρ
  have zg : ∀ m t, t ∉ Set.Ioo (1 / 2 : ℝ) 2 → gam ρ W m t = 0 := fun m t ht => gam_zero hWs ρ m ht
  have hE := continuous_exp_I_linear_form x₁ x₂
  have I_h : Integrable fun t : ℝ × ℝ =>
      h t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) := by
    refine (cutoff_product_integrable cW cW zW zW (hc 0 (by norm_num) 0 (by norm_num)) hE).congr (ae_of_all _ fun t => ?_)
    simp only [hh]
  have I_k : Integrable fun t : ℝ × ℝ =>
      regularised_kernel_product ρ W q t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) := by
    refine (((cutoff_product_integrable cW (cg 0) zW (zg 0) (hc 0 (by norm_num) 0 (by norm_num)) hE).add
      (cutoff_product_integrable cW (cg 1) zW (zg 1) (hc 0 (by norm_num) 1 (by norm_num)) hE)).add
      (cutoff_product_integrable cW (cg 2) zW (zg 2) (hc 0 (by norm_num) 2 le_rfl) hE)).congr (ae_of_all _ fun t => ?_)
    simp only [Pi.add_apply, regularised_kernel_product]; push_cast; ring
  have I_o : Integrable fun t : ℝ × ℝ =>
      oneMinusDD h t.1 t.2 * Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) := by
    have : Integrable fun t : ℝ × ℝ => ∑ m ∈ Finset.range 3, ∑ l ∈ Finset.range 3,
        ((gam ρ W m t.1 * gam ρ W l t.2 : ℝ) : ℂ) * q m l t.1 t.2 *
          Complex.exp (Complex.I * ((x₁ * t.1 + x₂ * t.2 : ℝ) : ℂ)) :=
      integrable_finsetSum _ fun m hm => integrable_finsetSum _ fun l hl =>
        cutoff_product_integrable (cg m) (cg l) (zg m) (zg l)
          (hc m (by have := Finset.mem_range.1 hm; omega) l (by have := Finset.mem_range.1 hl; omega)) hE
    refine this.congr (ae_of_all _ fun t => ?_)
    simp only [form, Finset.sum_mul]
  have csk : ∀ y, HasCompactSupport fun x => regularised_kernel_product ρ W q x y := fun y =>
    HasCompactSupport.intro (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)) fun x hx0 => by
      simp [regularised_kernel_product, zW x fun h => hx0 ⟨h.1.le, h.2.le⟩]
  have csh : ∀ x, HasCompactSupport fun y => h x y := fun x =>
    HasCompactSupport.intro (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)) fun y hy0 => by
      simp [hh, zW y fun h => hy0 ⟨h.1.le, h.2.le⟩]
  have sX := fourier_slice_in_x (K := oneMinusDD h) (K' := regularised_kernel_product ρ W q) x₁ x₂ ((1 + x₁ ^ 2 : ℝ) : ℂ) I_o I_k
    (fun y => by
      simp only [om_eq]
      exact Formalism.FourierDecayAlt.P.integration_by_parts_regularised (fun x => regularised_kernel_product ρ W q x y) (OUT y).1 (csk y) x₁)
  have sY := integral_slice_second_variable_eq (K := regularised_kernel_product ρ W q) (K' := h) x₁ x₂ ((1 + x₂ ^ 2 : ℝ) : ℂ) I_k I_h
    (fun x => by
      simp only [← (IN x).2]
      exact Formalism.FourierDecayAlt.P.integration_by_parts_regularised (fun y => h x y) (IN x).1 (csh x) x₂)
  rw [sX, sY]; push_cast; ring
end Formalism.FourierDecayAlt.P.B6
