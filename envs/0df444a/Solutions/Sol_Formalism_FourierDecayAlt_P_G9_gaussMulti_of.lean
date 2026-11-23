-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.gaussMulti_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:57.631377+00:00
-- url     : https://prove2.me/submissions/b3b82c96-efe7-4739-8af3-0432c58fe4bb

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_norm_det_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_gaussInt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_gaussOne_of_damped

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
theorem _root_.solution (hT : Takagi) (hG : GaussOneDamped) : GaussMulti := by
  intro d β t H hβ ht hH hdet
  obtain ⟨W, hW, σ, hσ, rfl⟩ := hT d H hH
  have hdW := norm_det_unitary hW
  have hd : ‖(W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) * Wᵀ).det‖ = ∏ k, σ k := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, norm_mul, norm_mul, hdW,
      one_mul, mul_one, norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (hσ k)]
  have hσ0 : ∀ k, σ k ≠ 0 := by
    intro k hk
    apply hdet
    rw [← norm_eq_zero, hd]
    exact Finset.prod_eq_zero (Finset.mem_univ k) hk
  have hfun : gaussInt β d (W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) * Wᵀ) t = fun δ : ℝ =>
      ∏ k, ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * psi β (((σ k : ℂ) / t) * w ^ 2 / 2) ∂(mu β) :=
    funext fun δ => gaussInt_eq d β t hβ W hW σ δ
  rw [hfun, hd]
  have hlim : ((‖t‖ ^ d / ∏ k, σ k : ℝ) : ℂ) = ∏ k : Fin d, (((‖(σ k : ℂ) / t‖)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod]
    congr 1
    have : ∀ k : Fin d, (‖(σ k : ℂ) / t‖)⁻¹ = ‖t‖ / σ k := by
      intro k
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hσ k), inv_div]
    simp_rw [this]
    rw [Finset.prod_div_distrib]
    simp
  rw [hlim]
  refine tendsto_finsetProd _ fun k _ => ?_
  exact gaussOne_of_damped hG β _ hβ (div_ne_zero (by exact_mod_cast hσ0 k) ht)
end Formalism.FourierDecayAlt.P.G9
