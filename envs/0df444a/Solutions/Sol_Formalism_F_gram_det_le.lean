-- Prove2me | solution 1 for Formalism.F.gram_det_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:29.355694+00:00
-- url     : https://prove2.me/submissions/f730a712-c517-42db-91c8-ae38c7ee867a

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
import Theorems.Thm_Formalism_F_normDet_le_pow_finrank
import Theorems.Thm_Formalism_F_linearCombinationMap_apply
import Theorems.Thm_Formalism_F_det_gram_eq_normDet_sq
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
end Formalism.F
end
end

set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution : GramDetLe := by
  intro E F _ _ _ _ ι _ _ v w C hC
  have hvw : ∀ c : EuclideanSpace ℝ ι,
      ‖linearCombinationMap w c‖ ≤ C * ‖linearCombinationMap v c‖ := by
    intro c
    simpa only [linearCombinationMap_apply] using hC (fun i => c i)
  by_cases hinj : Function.Injective (linearCombinationMap v)
  · rcases isEmpty_or_nonempty ι with hι | hι
    · simp [Matrix.det_isEmpty]
    have hC0 : 0 ≤ C := by
      by_contra hneg
      push_neg at hneg
      obtain ⟨i⟩ := hι
      have h1 := hvw (EuclideanSpace.single i 1)
      have h3 : ‖linearCombinationMap v (EuclideanSpace.single i 1)‖ ≤ 0 := by
        nlinarith [norm_nonneg (linearCombinationMap v (EuclideanSpace.single i 1)),
          norm_nonneg (linearCombinationMap w (EuclideanSpace.single i 1))]
      have h4 := hinj ((norm_le_zero_iff.1 h3).trans (map_zero _).symm)
      have h5 := congrArg (fun x : EuclideanSpace ℝ ι => x i) h4
      simp at h5
    let e := LinearEquiv.ofInjective (linearCombinationMap v) hinj
    let G : E →ₗ[ℝ] F := linearCombinationMap w ∘ₗ e.symm.toLinearMap ∘ₗ
      ((LinearMap.range (linearCombinationMap v)).orthogonalProjection :
        E →ₗ[ℝ] LinearMap.range (linearCombinationMap v))
    have hP : ∀ y : LinearMap.range (linearCombinationMap v),
        (LinearMap.range (linearCombinationMap v)).orthogonalProjection (y : E) = y := fun y =>
      Submodule.orthogonalProjection_mem_subspace_eq_self y
    have hGf : G ∘ₗ linearCombinationMap v = linearCombinationMap w := by
      ext c
      have : linearCombinationMap v c = (e c : E) := (LinearEquiv.ofInjective_apply _ c).symm
      simp only [G, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_toLinearMap]
      rw [this, hP, LinearEquiv.symm_apply_apply]
    have hb : ∀ y : LinearMap.range (linearCombinationMap v),
        ‖G.domRestrict (LinearMap.range (linearCombinationMap v)) y‖ ≤ C * ‖y‖ := by
      intro y
      have hy : linearCombinationMap v (e.symm y) = (y : E) := by
        rw [← LinearEquiv.ofInjective_apply (h := hinj) (linearCombinationMap v) (e.symm y)]
        exact congrArg Subtype.val (e.apply_symm_apply y)
      simp only [LinearMap.domRestrict_apply, G, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        LinearEquiv.coe_toLinearMap]
      rw [hP]
      calc ‖linearCombinationMap w (e.symm y)‖ ≤ C * ‖linearCombinationMap v (e.symm y)‖ := hvw _
        _ = C * ‖y‖ := by rw [hy]; rfl
    have hdom := normDet_le_pow_finrank (G.domRestrict (LinearMap.range (linearCombinationMap v))) C hC0 hb
    rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace] at hdom
    have hle : (linearCombinationMap w).normDet ≤
        C ^ Fintype.card ι * (linearCombinationMap v).normDet := by
      rw [← hGf, LinearMap.normDet_comp]
      exact mul_le_mul_of_nonneg_right hdom (LinearMap.normDet_nonneg _)
    rw [det_gram_eq_normDet_sq w, det_gram_eq_normDet_sq v]
    calc (linearCombinationMap w).normDet ^ 2
        ≤ (C ^ Fintype.card ι * (linearCombinationMap v).normDet) ^ 2 :=
          pow_le_pow_left₀ (LinearMap.normDet_nonneg _) hle 2
      _ = C ^ (2 * Fintype.card ι) * (linearCombinationMap v).normDet ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm (Fintype.card ι) 2]
  · rw [← LinearMap.ker_eq_bot] at hinj
    obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hinj
    have hw0 : linearCombinationMap w c = 0 := by
      have h1 := hvw c
      rw [LinearMap.mem_ker.1 hc, norm_zero, mul_zero] at h1
      exact norm_le_zero_iff.1 h1
    rw [det_gram_eq_zero_of_linearCombination_eq_zero w c hc0 hw0]
    exact mul_nonneg (by rw [pow_mul]; positivity) (Matrix.posSemidef_gram ℝ v).det_nonneg
end Formalism.F
