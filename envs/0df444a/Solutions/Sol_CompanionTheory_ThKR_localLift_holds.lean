-- Prove2me | solution 1 for CompanionTheory.ThKR.localLift_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:18:14.648585+00:00
-- url     : https://prove2.me/submissions/7b99e52c-b628-419a-8bbe-ef900a259677

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
import Theorems.Thm_CompanionTheory_ThKR_LL_det_bl
import Theorems.Thm_CompanionTheory_ThKR_LL_block_inl_inl_one
import Theorems.Thm_CompanionTheory_ThKR_LL_block_inl_inr_one
import Theorems.Thm_CompanionTheory_ThKR_LL_block_inr_inl_one
import Theorems.Thm_CompanionTheory_ThKR_LL_hasDerivAt_lin_exp
import Theorems.Thm_CompanionTheory_ThKR_LL_exp_mul_exp_neg
import Theorems.Thm_CompanionTheory_ThKR_LL_sympl_exp
import Theorems.Thm_CompanionTheory_ThKR_LL_intw_of_sympl
import Theorems.Thm_CompanionTheory_ThKR_LL_quad_eq
import Theorems.Thm_CompanionTheory_ThKR_LL_differentiableAt_det
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_dRho
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_differentiableAt
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_hasDerivAt
import Theorems.Thm_CompanionTheory_ThKR_LL_big_one
import Theorems.Thm_CompanionTheory_ThKR_LL_isUnit_big
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_big
import Theorems.Thm_CompanionTheory_ThKR_LL_ld_big
import Theorems.Thm_GlobalTheory_RealWeil_quad_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR
open LL
namespace CompanionTheory.ThKR
theorem _root_.solution : LocalLift := by
  intro l _ _ X hX
  let g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => NormedSpace.exp (t • X)
  have g0 : g 0 = 1 := by simp [g]
  have hd := fun i j t => hasDerivAt_lin_exp (bl i j) X t
  let A : ℝ → Eu l →L[ℝ] Eu l := fun t => bl Sum.inl Sum.inl (g t)
  let c : ℝ → ℝ := fun t => (√|(A t).det|)⁻¹
  let V : ℝ → Sch l →L[ℂ] Sch l := fun t =>
    big (Ring.inverse (A t)) (bl Sum.inl Sum.inr (g t)) (bl Sum.inr Sum.inl (g t)) (c t)
  have A0 : A 0 = 1 := by simp only [A, g0, block_inl_inl_one]
  have hopen : ∀ t, IsUnit (A t) → ∀ᶠ u in 𝓝 t, IsUnit (A u) := fun t ht =>
    (hd _ _ t).continuousAt.eventually (Units.isOpen.mem_nhds ht)
  have hdet : ∀ t, IsUnit (A t) → (Ring.inverse (A t)).det * (A t).det = 1 := fun t ht => by
    have := congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ ht)
    simpa [ContinuousLinearMap.det] using this
  have hne : ∀ t, IsUnit (A t) → (A t).det ≠ 0 := fun t ht => right_ne_zero_of_mul_eq_one (hdet t ht)
  have hc : ∀ t, IsUnit (A t) → c t ^ 2 = |(Ring.inverse (A t)).det| := fun t ht => by
    rw [eq_inv_of_mul_eq_one_left (hdet t ht), abs_inv, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have hc0 : ∀ t, IsUnit (A t) → c t ≠ 0 := fun t ht =>
    inv_ne_zero (Real.sqrt_pos.2 (abs_pos.2 (hne t ht))).ne'
  have hcd : ∀ t, IsUnit (A t) → DifferentiableAt ℝ c t := fun t ht => by
    have h1 : DifferentiableAt ℝ (fun t => (A t).det) t := by
      simp only [A, det_bl]
      exact differentiableAt_det fun i j =>
        (hasDerivAt_lin_exp (Matrix.entryLinearMap ℝ ℝ (Sum.inl i) (Sum.inl j)) X t).differentiableAt
    exact ((h1.abs (hne t ht)).sqrt (abs_pos.2 (hne t ht)).ne').inv (Real.sqrt_pos.2 (abs_pos.2 (hne t ht))).ne'
  have c0 : c 0 = 1 := by simp [c, A0, ContinuousLinearMap.det]
  have V0 : V 0 = 1 := by simp only [V, A0, g0, c0, block_inl_inr_one, block_inr_inl_one, Ring.inverse_one, big_one]
  have hU : ∀ t, IsUnit (A t) → IsUnit (V t) := fun t ht => isUnit_big ht.ringInverse _ _ (hc0 t ht)
  have hI : ∀ t, IsUnit (A t) → Impl (fun w => g t *ᵥ w) (V t).toLinearMap := fun t ht =>
    ⟨iso_big ht.ringInverse _ _ (hc t ht), fun w => intw_of_sympl (sympl_exp (SMulMemClass.smul_mem t hX)) ht _ w⟩
  let v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ) := fun t w => NormedSpace.exp (t • -X) *ᵥ w
  have hv : ∀ t w a, HasDerivAt (fun t => v t w a) (((NormedSpace.exp (t • -X) * -X) *ᵥ w) a) t := fun t w a =>
    hasDerivAt_lin_exp ((LinearMap.proj a).comp ((Matrix.mulVecBilin ℝ ℝ).flip w)) (-X) t
  have hw : ∀ t, IsUnit (A t) → ∀ w f, dRho w (V t f) = V t (dRho (v t w) f) := fun t ht w f => by
    have hs : Function.Surjective (V t).toLinearMap := fun f => ⟨Ring.inverse (V t) f, by
      show (V t * Ring.inverse (V t)) f = f
      rw [Ring.mul_inverse_cancel _ (hU t ht), ContinuousLinearMap.one_apply]⟩
    have := Impl.dRho (s := Matrix.mulVecLin (g t)) (hI t ht) hs (v t w) f
    simp only [v, g, Matrix.mulVecLin_apply, mulVec_mulVec, smul_neg, exp_mul_exp_neg, one_mulVec] at this
    simp only [v, smul_neg]
    exact this.symm
  have hL := fun t (ht : IsUnit (A t)) (Ai' : Eu l →L[ℝ] Eu l) (h : HasDerivAt (fun t => Ring.inverse (A t)) Ai' t) =>
    ld_big h (hd Sum.inl Sum.inr t) (hd Sum.inr Sum.inl t) (hcd t ht).hasDerivAt
      ((hopen t ht).mono fun u hu => ⟨hu.ringInverse, hc u hu⟩)
  have h0 : IsUnit (A 0) := A0 ▸ isUnit_one
  obtain ⟨ε, hε, hA⟩ := Metric.eventually_nhds_iff.1 (hopen 0 h0)
  simp only [dist_zero_right, Real.norm_eq_abs] at hA
  refine ⟨ε, V, fun t => Ring.inverse (V t), (deriv c 0 : ℝ) + ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ), hε,
    fun f => by rw [V0]; rfl, fun t ht => ⟨fun f => ?_, fun f => ?_, hI t (hA ht)⟩, fun t ht f lam => ?_, fun f lam => ?_⟩
  · rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ (hU t (hA ht)), ContinuousLinearMap.one_apply]
  · rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ (hU t (hA ht)), ContinuousLinearMap.one_apply]
  · obtain ⟨Q, hQ, -⟩ := hL t (hA ht) _ ((hd Sum.inl Sum.inl t).differentiableAt.inverse (hA ht)).hasDerivAt
    exact hQ.differentiableAt v (fun w a => (hv t w a).differentiableAt) ((hopen t (hA ht)).mono hw) f lam
  · have h1 : HasDerivAt (fun t => Ring.inverse (A t)) (-bl Sum.inl Sum.inl X) 0 := by
      have h2 := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Eu l →L[ℝ] Eu l)ˣ)).comp_hasDerivAt_of_eq 0
        (hd Sum.inl Sum.inl 0) A0.symm
      exact h2.congr_deriv (by
        simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, inv_one, Units.val_one,
          one_mul, mul_one, zero_smul, NormedSpace.exp_zero])
    obtain ⟨Q, hQ, hQ'⟩ := hL 0 h0 _ h1
    have h3 := hQ' (by rw [A0, Ring.inverse_one]) (by rw [← block_inl_inr_one, ← g0]) (by rw [← block_inr_inl_one, ← g0]) c0
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h3
    set z : ℂ := (deriv c 0 : ℝ) + ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) with hz
    have h4 : Q = ⇑(quad X + z • (1 : Sch l →L[ℂ] Sch l)) := by
      funext f
      rw [h3, ContinuousLinearMap.add_apply, quad_eq hX, hz, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        add_smul]
      abel
    rw [h4] at hQ
    refine hQ.hasDerivAt (fun f => ?_) v (fun w => X *ᵥ w) (fun w => by simp [v]) (fun w a => ?_) (fun w => ?_)
      ((hopen 0 h0).mono hw) f lam
    · exact congrArg (fun T : Sch l →L[ℂ] Sch l => T f) V0
    · simpa [neg_mulVec] using hv 0 w a
    · rw [← quad_comm hX, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      abel
end CompanionTheory.ThKR
