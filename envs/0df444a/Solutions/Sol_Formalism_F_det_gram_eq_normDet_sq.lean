-- Prove2me | solution 1 for Formalism.F.det_gram_eq_normDet_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:08.219796+00:00
-- url     : https://prove2.me/submissions/a818de69-ab4c-4fd2-9a4d-64b30cda98fd

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
import Theorems.Thm_Formalism_F_linearCombinationMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module
noncomputable section
namespace Formalism.F
private theorem det_gram_eq_zero_of_linearCombination_eq_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) (c : EuclideanSpace ℝ ι) (hc : c ≠ 0)
    (h0 : linearCombinationMap v c = 0) : (Matrix.gram ℝ v).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun i => c i, ?_, ?_⟩
  · intro h
    apply hc
    ext i
    exact congrFun h i
  · ext i
    rw [linearCombinationMap_apply] at h0
    have h1 : inner ℝ (v i) (∑ j, c j • v j) = 0 := by rw [h0, inner_zero_right]
    rw [inner_sum] at h1
    simpa [Matrix.mulVec, dotProduct, Matrix.gram_apply, real_inner_smul_right, mul_comm] using h1
private theorem gram_linearCombinationMap_eq_toMatrix {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (v : ι → E)
    (b : OrthonormalBasis κ ℝ (EuclideanSpace ℝ ι)) :
    Matrix.gram ℝ (fun k => linearCombinationMap v (b k)) =
      LinearMap.toMatrix b.toBasis b.toBasis
        (LinearMap.adjoint (linearCombinationMap v).rangeRestrict ∘ₗ (linearCombinationMap v).rangeRestrict) := by
  ext k l
  rw [Matrix.gram_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, OrthonormalBasis.repr_apply_apply,
    LinearMap.adjoint_inner_right]
  rfl
end Formalism.F
end
end

set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) :
    (Matrix.gram ℝ v).det = (linearCombinationMap v).normDet ^ 2 := by
  have hv : v = fun i => linearCombinationMap v (EuclideanSpace.basisFun ι ℝ i) := by
    funext i
    rw [linearCombinationMap_apply]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, ite_smul]
  have h1 : (Matrix.gram ℝ v).det = LinearMap.det (LinearMap.adjoint (linearCombinationMap v).rangeRestrict ∘ₗ
      (linearCombinationMap v).rangeRestrict) := by
    conv_lhs => rw [hv]
    rw [gram_linearCombinationMap_eq_toMatrix, LinearMap.det_toMatrix]
  unfold LinearMap.normDet
  split_ifs with h
  · have h2 : (Matrix.gram ℝ (fun k => linearCombinationMap v (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) k))).det =
        LinearMap.det (LinearMap.adjoint (linearCombinationMap v).rangeRestrict ∘ₗ
          (linearCombinationMap v).rangeRestrict) := by
      rw [gram_linearCombinationMap_eq_toMatrix, LinearMap.det_toMatrix]
    rw [h1, ← h2]
    have hG : Matrix.gram ℝ (fun k => linearCombinationMap v (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) k)) =
        (LinearMap.toMatrix (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι)).toBasis h.some.toBasis
          (linearCombinationMap v).rangeRestrict).transpose *
        LinearMap.toMatrix (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι)).toBasis h.some.toBasis
          (linearCombinationMap v).rangeRestrict := by
      ext k l
      rw [Matrix.gram_apply, Matrix.mul_apply]
      simp only [Matrix.transpose_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis]
      have e1 : inner ℝ (linearCombinationMap v (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) k))
          (linearCombinationMap v (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) l)) =
          inner ℝ ((linearCombinationMap v).rangeRestrict (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) k))
            ((linearCombinationMap v).rangeRestrict (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι) l)) := rfl
      rw [e1, ← h.some.sum_inner_mul_inner]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [real_inner_comm (h.some m) ((linearCombinationMap v).rangeRestrict _),
        ← OrthonormalBasis.repr_apply_apply, ← OrthonormalBasis.repr_apply_apply]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, Real.norm_eq_abs, sq_abs, sq]
  · rw [zero_pow two_ne_zero]
    have hni : ¬ Function.Injective (linearCombinationMap v) := by
      intro hinj
      exact h ⟨(stdOrthonormalBasis ℝ (LinearMap.range (linearCombinationMap v))).reindex
        (finCongr (LinearMap.finrank_range_of_inj hinj))⟩
    rw [← LinearMap.ker_eq_bot] at hni
    obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hni
    exact det_gram_eq_zero_of_linearCombination_eq_zero v c hc0 (LinearMap.mem_ker.1 hc)
end Formalism.F
