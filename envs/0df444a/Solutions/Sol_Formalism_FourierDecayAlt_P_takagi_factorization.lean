-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.takagi_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:40.627189+00:00
-- url     : https://prove2.me/submissions/d5113044-4814-45e4-9e42-bc35f09ac509

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_exists_takagi_family
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_takMap_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_takMap_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
open Module
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.Takagi := by
  intro d H hH
  obtain ⟨e, σ, he, -, hσ, hTe⟩ := Formalism.FourierDecayAlt.P.G9.exists_takagi_family (Formalism.FourierDecayAlt.P.G9.takMap H)
    (Formalism.FourierDecayAlt.P.G9.takMap_symm H hH) d ⊤ (by simp) (fun _ _ => Submodule.mem_top)
  set W : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => e j i with hW
  have h1 : star W * W = 1 := by
    ext i j
    have h := (orthonormal_iff_ite.1 he) i j
    rw [PiLp.inner_apply] at h
    simp only [RCLike.inner_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hW, Matrix.star_apply, mul_comm]
  have h2 : W * star W = 1 := mul_eq_one_comm.1 h1
  have h3 : H * W.map conj = W * Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) := by
    ext i j
    have h := congrFun (congrArg WithLp.ofLp (hTe j)) i
    have h' : Formalism.FourierDecayAlt.P.G9.takMap H (e j) i = (σ j : ℂ) * e j i := by simpa using h
    rw [Formalism.FourierDecayAlt.P.G9.takMap_apply] at h'
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [Matrix.map_apply, hW, Matrix.of_apply]
    rw [h', mul_comm]
  have h4 : W.map conj * W.transpose = 1 := by
    have h := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h
    rw [← h]
    congr 1
  refine ⟨W, Matrix.mem_unitaryGroup_iff.2 h2, σ, hσ, ?_⟩
  rw [← h3, Matrix.mul_assoc, h4, Matrix.mul_one]
end Formalism.FourierDecayAlt.P
