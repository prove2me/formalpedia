-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.gaussMultiOfOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:55.883419+00:00
-- url     : https://prove2.me/submissions/14c80b0e-ca20-4b8b-9c7f-01d4d014d7b6

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_normSq_det_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_gaussOne_of_damped
import Theorems.Thm_Formalism_FourierDecayAlt_P_G8_gaussInt_takagi

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
theorem _root_.solution : GaussMultiOfOne := by
  intro hT hU hG d β t H hβ ht hsym hdet
  obtain ⟨W, hW, σ, hσ, hH⟩ := hT d H hsym
  have hnW : ‖W.det‖ = 1 := by
    have h := normSq_det_unitary d W hW
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg W.det, sq_nonneg (‖W.det‖ - 1)]
  have hdH : H.det = W.det * (∏ k, ((σ k : ℝ) : ℂ)) * W.det := by
    rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
  have hσ0 : ∀ k, σ k ≠ 0 := by
    intro k hk
    apply hdet
    rw [hdH, Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; simp)]
    simp
  have hkey : gaussInt β d H t = fun δ => ∏ k, ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) *
      psi β (((σ k : ℂ) / t) * w ^ 2 / 2) ∂(mu β) := by
    funext δ; rw [hH]; exact gaussInt_takagi hU d β t W hW σ δ
  have hlim : ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ) = ∏ k : Fin d, (((‖(σ k : ℂ) / t‖)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod]
    congr 1
    rw [hdH, norm_mul, norm_mul, hnW, norm_prod]
    simp only [norm_div, inv_div, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, one_mul, mul_one]
  rw [hkey, hlim]
  refine tendsto_finsetProd _ fun k _ => ?_
  exact gaussOne_of_damped hG β _ hβ (div_ne_zero (by exact_mod_cast hσ0 k) ht)
end Formalism.FourierDecayAlt.P.G8
