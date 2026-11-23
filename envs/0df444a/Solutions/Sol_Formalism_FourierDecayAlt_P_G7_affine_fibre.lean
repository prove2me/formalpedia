-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.affine_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:19.912698+00:00
-- url     : https://prove2.me/submissions/ca3ae71a-4682-4f2d-af4d-a91a9a40b8b5

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_affine_change_of_variables


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (β : ℂ)
    (α γ : Y → ℂ) (hα : Measurable α) (hγ : Measurable γ) (h0 : ∀ᵐ y ∂ν, α y ≠ 0) :
    Measure.map (fun p : ℂ × Y => (α p.2 * p.1 + γ p.2, p.2))
      (((mu β).prod ν).withDensity (fun p => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal))) = (mu β).prod ν := by
  have hT : Measurable (fun p : ℂ × Y => (α p.2 * p.1 + γ p.2, p.2)) := by fun_prop
  have hd : Measurable (fun p : ℂ × Y => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal)) := by fun_prop
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hfT : Measurable (fun p : ℂ × Y => f (α p.2 * p.1 + γ p.2, p.2)) := hf.comp hT
  rw [lintegral_map hf hT, lintegral_withDensity_eq_lintegral_mul _ hd hfT,
    lintegral_prod_symm _ (hd.mul hfT).aemeasurable, lintegral_prod_symm _ hf.aemeasurable]
  refine lintegral_congr_ae (h0.mono fun y hy => ?_)
  have hfy : Measurable (fun x : ℂ => f (x, y)) := hf.comp (by fun_prop)
  have hA := affine_change_of_variables β (α y) (γ y) hy
  have h1 : ∫⁻ x, f (α y * x + γ y, y) ∂(mu β) =
      ((Real.toNNReal ((‖α y‖ ^ 2)⁻¹) : NNReal) : ENNReal) * ∫⁻ x, f (x, y) ∂(mu β) := by
    rw [← lintegral_map hfy (by fun_prop : Measurable fun x : ℂ => α y * x + γ y), hA, ENNReal.smul_def,
      lintegral_smul_measure, smul_eq_mul]
  have hfy2 : Measurable (fun x : ℂ => f (α y * x + γ y, y)) :=
    hfy.comp (by fun_prop : Measurable fun x : ℂ => α y * x + γ y)
  simp only [Pi.mul_apply]
  rw [lintegral_const_mul _ hfy2, h1, ← mul_assoc,
    ← ENNReal.coe_mul]
  have h2 : ‖α y‖₊ ^ 2 * Real.toNNReal ((‖α y‖ ^ 2)⁻¹) = 1 := by
    have hpos : (0 : ℝ) < ‖α y‖ ^ 2 := by positivity
    apply NNReal.eq
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
    simp only [NNReal.coe_pow, coe_nnnorm, NNReal.coe_one]
    exact mul_inv_cancel₀ hpos.ne'
  rw [h2, ENNReal.coe_one, one_mul]
end Formalism.FourierDecayAlt.P.G7
