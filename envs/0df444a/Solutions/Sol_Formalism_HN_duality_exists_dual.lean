-- Prove2me | solution 1 for Formalism.HN.duality_exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:25.185702+00:00
-- url     : https://prove2.me/submissions/4e51c7f8-2950-4758-be39-bea898a45fee

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Theorems.Thm_Formalism_HN_duality_eq_zero_of_inner
import Theorems.Thm_Formalism_F_gram_sum_smul_eq_transpose_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.HN
theorem _root_.solution (v : ι → E) (hv : LinearIndependent ℝ v) :
    ∃ w : ι → E, (∀ i, w i ∈ span ℝ (Set.range v)) ∧
      (∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) ∧
      (Matrix.gram ℝ w).det = ((Matrix.gram ℝ v).det)⁻¹ := by
  have hGdet : (Matrix.gram ℝ v).det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hc0
    have hz : ∑ i, c i • v i = 0 := by
      refine duality_eq_zero_of_inner v
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_range_self i))) fun k => ?_
      have hk : ∑ i, Matrix.gram ℝ v k i * c i = 0 := congrFun hc k
      rw [inner_sum, ← hk]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right, Matrix.gram_apply, mul_comm]
    funext i
    exact Fintype.linearIndependent_iff.mp hv c hz i
  have hunit : IsUnit (Matrix.gram ℝ v).det := isUnit_iff_ne_zero.mpr hGdet
  have hmul : Matrix.gram ℝ v * (Matrix.gram ℝ v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hmul' : (Matrix.gram ℝ v)⁻¹ * Matrix.gram ℝ v = 1 := Matrix.nonsing_inv_mul _ hunit
  refine ⟨fun i => ∑ j, (Matrix.gram ℝ v)⁻¹ j i • v j,
    fun i => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j)), fun k i => ?_, ?_⟩
  · show inner ℝ (v k) (∑ j, (Matrix.gram ℝ v)⁻¹ j i • v j) = if k = i then 1 else 0
    have h := congrFun (congrFun hmul k) i
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [inner_sum, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right, Matrix.gram_apply, mul_comm]
  · show (Matrix.gram ℝ (fun i => ∑ j, (Matrix.gram ℝ v)⁻¹ j i • v j)).det = _
    rw [Formalism.F.gram_sum_smul_eq_transpose_mul v (Matrix.gram ℝ v)⁻¹, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose]
    have h1 : ((Matrix.gram ℝ v)⁻¹).det * (Matrix.gram ℝ v).det = 1 := by
      rw [← Matrix.det_mul, hmul', Matrix.det_one]
    rw [h1, one_mul]
    exact eq_inv_of_mul_eq_one_left h1
end Formalism.HN
