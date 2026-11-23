-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.diagF_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:43.728801+00:00
-- url     : https://prove2.me/submissions/622a9aa2-10aa-4806-8afb-711ca5107858

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_psi_sum

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
theorem _root_.solution (β : ℂ) (d : ℕ) (σ : Fin d → ℝ) (t : ℂ) (δ : ℝ) (y : Fin d → ℂ) :
    diagF β d σ t δ y =
      ∏ k, (((Real.exp (-δ * ‖y k‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * (y k) ^ 2 / 2)) := by
  rw [Finset.prod_mul_distrib, ← psi_sum, ← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum, diagF]
  congr 2
  simp only [dotProduct, Matrix.mulVec_diagonal, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_mul_eq_mul_div, div_div, mul_comm t 2]
  congr 1
  ring
end Formalism.FourierDecayAlt.P.G8
