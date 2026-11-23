-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.gaussInt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:14.516812+00:00
-- url     : https://prove2.me/submissions/29573f2f-0cdb-4607-bde2-5886ef1b0d8e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_unitary_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_sum_normSq_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_transpose_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_psi_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution (d : ℕ) (β t : ℂ) (hβ : β ≠ 0) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) (σ : Fin d → ℝ) (δ : ℝ) :
    gaussInt β d (W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) * Wᵀ) t δ =
      ∏ k, ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * w ^ 2 / 2) ∂(mu β) := by
  have hU := transpose_unitary hW
  have hmp := unitary_mp d β hβ Wᵀ hU
  have hinj : Function.Injective (fun x : Fin d → ℂ => Wᵀ *ᵥ x) := by
    intro x y hxy
    have h1 : (Wᵀ)ᴴ * Wᵀ = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    have := congrArg (fun v => (Wᵀ)ᴴ *ᵥ v) hxy
    simpa [Matrix.mulVec_mulVec, h1] using this
  have hemb : MeasurableEmbedding (fun x : Fin d → ℂ => Wᵀ *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurableEmbedding hinj
  have hsf : SigmaFinite (mu β) := by unfold mu; infer_instance
  rw [← integral_fintype_prod_eq_prod (μ := fun _ : Fin d => mu β)
    (fun (k : Fin d) (w : ℂ) => ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * w ^ 2 / 2))]
  change _ = ∫ y : Fin d → ℂ, _ ∂(muPi β (Fin d))
  rw [← hmp.integral_comp hemb]
  unfold gaussInt
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Finset.prod_mul_distrib, ← psi_sum, ← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum,
    sum_normSq_unitary hU]
  congr 2
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases ht : t = 0
  · simp [ht]
  · field_simp
end Formalism.FourierDecayAlt.P.G9
