-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.secEx_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:17.401562+00:00
-- url     : https://prove2.me/submissions/5a9fb932-8d43-461d-b377-3061a533d8bc

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MapOfRealMul
import Theorems.Thm_CompanionTheory_ThKR_Mp_C_dd_mul_eq
import Theorems.Thm_CompanionTheory_ThKR_Mp_C_isSymm_inv_mul
import Theorems.Thm_CompanionTheory_ThKR_Mp_C_sympl_sp
import Theorems.Thm_CompanionTheory_ThKR_Mp_C_sec_apply_zero
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_smul
import Theorems.Thm_CompanionTheory_ThKR_LL_Iso_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_smul
import Theorems.Thm_CompanionTheory_ThKR_LL_det_bl
import Theorems.Thm_CompanionTheory_ThKR_LL_intw_of_sympl
import Theorems.Thm_CompanionTheory_ThKR_LL_isUnit_big
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_big


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open C
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution (h1 : MkElt l) (h2 : NrmUp l) : SecEx l := by
  intro s hd
  have hu : IsUnit s.1.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  let uA : (Eu l →L[ℝ] Eu l)ˣ :=
    ⟨Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁⁻¹,
      by rw [← map_mul, mul_nonsing_inv _ hu, map_one], by rw [← map_mul, nonsing_inv_mul _ hu, map_one]⟩
  have hA : IsUnit (bl Sum.inl Sum.inl s.1) := ⟨uA, rfl⟩
  have hinv : Ring.inverse (bl Sum.inl Sum.inl s.1) = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁⁻¹ :=
    Ring.inverse_unit uA
  have hAiB : Ring.inverse (bl Sum.inl Sum.inl s.1) * bl Sum.inl Sum.inr s.1 =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂) := by
    rw [hinv, map_mul]
    rfl
  have hdA : (bl Sum.inl Sum.inl s.1).det = s.1.toBlocks₁₁.det := det_bl _ _ _
  have hdet : (Ring.inverse (bl Sum.inl Sum.inl s.1)).det * (bl Sum.inl Sum.inl s.1).det = 1 := by
    have := congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ hA)
    simpa [ContinuousLinearMap.det] using this
  set c : ℝ := (√|s.1.toBlocks₁₁.det|)⁻¹ with hcdef
  have hcsq : c ^ 2 = |s.1.toBlocks₁₁.det|⁻¹ := by
    rw [hcdef, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have hc : c ^ 2 = |(Ring.inverse (bl Sum.inl Sum.inl s.1)).det| := by
    rw [hcsq, eq_inv_of_mul_eq_one_left hdet, hdA, abs_inv]
  have hc0 : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 (abs_pos.2 hd)).ne'
  obtain ⟨z, hz1, hz, hzpos⟩ : ∃ z : ℂ, ‖z‖ = 1 ∧ z ^ 2 * ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = 1 ∧
      (0 < s.1.toBlocks₁₁.det → z = 1) := by
    by_cases hpos : 0 < s.1.toBlocks₁₁.det
    · have e : c ^ 2 * s.1.toBlocks₁₁.det = 1 := by
        rw [hcsq, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
      refine ⟨1, by simp, ?_, fun _ => rfl⟩
      have e2 : ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = ((c ^ 2 * s.1.toBlocks₁₁.det : ℝ) : ℂ) := by push_cast; ring
      rw [e2, e]
      simp
    · have hneg : s.1.toBlocks₁₁.det < 0 := lt_of_le_of_ne (not_lt.1 hpos) hd
      have e : c ^ 2 * s.1.toBlocks₁₁.det = -1 := by
        rw [hcsq, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hd]
      refine ⟨I, by simp, ?_, fun h => absurd h hpos⟩
      have e2 : ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = ((c ^ 2 * s.1.toBlocks₁₁.det : ℝ) : ℂ) := by push_cast; ring
      rw [e2, e, I_sq]
      push_cast
      ring
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1
  have hU : IsUnit (z • sec s.1) := by
    rw [Algebra.smul_def]
    exact ((IsUnit.mk0 z hz0).map _).mul (isUnit_big hA.ringInverse _ _ hc0)
  have hiso := iso_big hA.ringInverse (bl Sum.inl Sum.inr s.1) (bl Sum.inr Sum.inl s.1) hc
  have hI : Impl (fun w => s.1 *ᵥ w) (z • sec s.1).toLinearMap := by
    refine ⟨fun f => ?_, fun w => (intw_of_sympl (sympl_sp s) hA c w).smul z⟩
    show ‖schwartzToL2 l ((z • sec s.1) f)‖ = ‖schwartzToL2 l f‖
    rw [ContinuousLinearMap.smul_apply, map_smul, norm_smul, hz1, one_mul]
    exact hiso f
  have hN : Nrm s.1 (z • sec s.1) := by
    intro s' f hf
    have key := h2 _ (isSymm_inv_mul s hd) s' f hf
    have ev : (z • sec s.1) f 0 = z * ((c : ℂ) *
        fou l (ph (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂))) (fouInv l f)) 0) := by
      rw [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, sec_apply_zero s.1 hA f, hAiB]
    rw [ev, dd_mul_eq s.1 s'.1 hd, ← key]
    calc _ = (z ^ 2 * ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ))) *
          ((fou l (ph (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂))) (fouInv l f)) 0) ^ 2 *
            (upperParabolic s'.1 + (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂).map Complex.ofReal * loQ s'.1).det) := by ring
      _ = _ := by rw [hz, one_mul]
  obtain ⟨g, hg1, hg2⟩ := h1 s _ hU hI hN
  exact ⟨g, z, hg1, hg2, hzpos⟩
end CompanionTheory.ThKR.Mp
