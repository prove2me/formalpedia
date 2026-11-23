-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.gaussInt_takagi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:38.563867+00:00
-- url     : https://prove2.me/submissions/0b82d741-80ad-4941-ab04-5b29668540c5

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_transpose_mem_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_sum_norm_sq_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_quad_form_takagi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_continuous_diagF
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_diagF_eq_prod

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
theorem _root_.solution (hU : UnitaryInvariant) (d : ℕ) (β t : ℂ) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) (σ : Fin d → ℝ) (δ : ℝ) :
    gaussInt β d (W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) * Wᵀ) t δ =
      ∏ k, ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * w ^ 2 / 2) ∂(mu β) := by
  have hWt := transpose_mem_unitary d W hW
  have hmp := hU d β Wᵀ hWt
  have h1 : gaussInt β d (W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) * Wᵀ) t δ =
      ∫ x : Fin d → ℂ, diagF β d σ t δ (Wᵀ *ᵥ x) ∂(muPi β (Fin d)) := by
    unfold gaussInt diagF
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [quad_form_takagi, sum_norm_sq_unitary d Wᵀ hWt x]
  rw [h1, ← integral_map hmp.measurable.aemeasurable
    (continuous_diagF β d σ t δ).aestronglyMeasurable, hmp.map_eq]
  simp_rw [diagF_eq_prod]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin d => mu β)
    (fun k w => ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * w ^ 2 / 2))
end Formalism.FourierDecayAlt.P.G8
