-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.integral_gK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:44.072381+00:00
-- url     : https://prove2.me/submissions/5750ac63-cce2-423e-94b9-dfef587ad61a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_cpow_half_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_integrable_gK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution (δ p q : ℝ) (hδ : 0 < δ) :
    ∫ z : ℝ × ℝ, gK δ p q z = ((Real.pi / Real.sqrt (δ ^ 2 + p ^ 2 + q ^ 2) : ℝ) : ℂ) := by
  have hR : 0 < δ ^ 2 + p ^ 2 + q ^ 2 := by positivity
  set u : ℂ := (δ : ℂ) + Complex.I * p with hu
  have hure : u.re = δ := by simp [hu]
  have hu0 : u ≠ 0 := by intro h; rw [h] at hure; simp at hure; exact hδ.ne hure
  rw [Measure.volume_eq_prod, integral_prod _ (integrable_gK δ p q hδ)]
  have hin : ∀ x : ℝ, ∫ y : ℝ, gK δ p q (x, y) =
      ((Real.pi : ℂ) / u) ^ (1 / 2 : ℂ) *
        Complex.exp (-(((δ ^ 2 + p ^ 2 + q ^ 2 : ℝ) : ℂ) / u) * (x : ℂ) ^ 2) := by
    intro x
    show ∫ y : ℝ, Complex.exp (-u * (y : ℂ) ^ 2 + (-2 * Complex.I * q * x) * (y : ℂ) +
      -((δ : ℂ) - Complex.I * p) * (x : ℂ) ^ 2) = _
    rw [integral_cexp_quadratic (by rw [Complex.neg_re, hure]; linarith)]
    rw [neg_neg]
    congr 2
    have hconj : ((δ : ℂ) - Complex.I * p) * u = (δ : ℂ) ^ 2 + (p : ℂ) ^ 2 := by
      rw [hu]; linear_combination (-(p:ℂ)^2) * Complex.I_sq
    obtain ⟨v, hv⟩ : ∃ v : ℂ, v = (δ : ℂ) - Complex.I * p := ⟨_, rfl⟩
    rw [← hv] at hconj ⊢
    clear_value u
    push_cast
    field_simp
    linear_combination (-4 * (x:ℂ)^2) * hconj + (4 * (q:ℂ)^2 * (x:ℂ)^2) * Complex.I_sq
  simp_rw [hin]
  rw [integral_const_mul, integral_gaussian_complex, cpow_half_mul u (by rw [hure]; exact hδ) _ hR]
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero, hure]
  have : 0 < Complex.normSq u := Complex.normSq_pos.2 hu0
  positivity
end Formalism.FourierDecayAlt.P.G8
