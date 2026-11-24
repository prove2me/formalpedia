-- Prove2me | solution 1 for Formalism.L2.Th1.H.gauss_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:52:55.913555+00:00
-- url     : https://prove2.me/submissions/821982ce-7323-42f5-bad1-3ffbf15e9307

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyGaussianIntegral
import Theorems.Thm_Formalism_L2_Th1_H_gauss_plane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {n : Type*} [Fintype n] (l : n → ℂ) (hl : ∀ i, 0 < (l i).re) :
    Integrable (fun w : n → ℂ => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2)) ∧
      ∫ w : n → ℂ, Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2) = (∏ i, l i)⁻¹ := by
  have hfun : (fun w : n → ℂ => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2)) =
      fun w => ∏ i, Complex.exp (-((Real.pi : ℂ) * l i) * ((‖w i‖ : ℝ) : ℂ) ^ 2) := by
    funext w
    rw [← Complex.exp_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hfun]
  refine ⟨?_, ?_⟩
  · exact Integrable.fintype_prod
      (f := fun i (z : ℂ) => Complex.exp (-((Real.pi : ℂ) * l i) * ((‖z‖ : ℝ) : ℂ) ^ 2))
      (fun i => (gauss_plane (l i) (hl i)).1)
  · rw [integral_fintype_prod_volume_eq_prod
      (fun i (z : ℂ) => Complex.exp (-((Real.pi : ℂ) * l i) * ((‖z‖ : ℝ) : ℂ) ^ 2)),
      ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => (gauss_plane (l i) (hl i)).2
end Formalism.L2.Th1.H
