-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.gaussian_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:47.043351+00:00
-- url     : https://prove2.me/submissions/d36c8fab-090a-4592-be70-8fe1c1e3d998

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GaussianIntegralFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : ComplexGaussianIntegral := by
  intro ι _ w hw
  have h1 : ∀ z : ι → ℂ, Real.exp (-∑ j, w j * ‖z j‖ ^ 2) =
      ∏ j, (fun (j : ι) (x : ℂ) => Real.exp (-w j * ‖x‖ ^ 2)) j (z j) := by
    intro z
    rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h2 := integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (E := fun _ : ι => ℂ)
    (fun (j : ι) (x : ℂ) => Real.exp (-w j * ‖x‖ ^ 2))
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), h2]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (hw j)]
  simp [Complex.finrank_real_complex]
end Formalism.HermitianLattices.GenusMassVolumes
