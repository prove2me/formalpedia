-- Prove2me | solution 1 for Formalism.MainStatements.RankOne.KD.approx_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:34:14.902+00:00
-- url     : https://prove2.me/submissions/0ff25d1d-f686-4299-85e9-7e7784ed5647

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_AutomorphicTheory_RankOneTori_KDense
import Theorems.Thm_Formalism_MainStatements_RankOne_KD_int_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_sub
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_IsFam_sub
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open Formalism Formalism.MainStatements Formalism.MainStatements.RankOne Formalism.MainStatements.RankOne.KD
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
variable [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]
namespace Formalism.MainStatements.RankOne.KD
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (μ : Measure Γ)
    [IsFiniteMeasure μ] [IsOpenPosMeasure μ] (A : Subalgebra ℝ C(Γ, ℝ)) (hA : A.SeparatesPoints) {ι : Type} [Fintype ι]
    {F : ι → Γ → V} (hF : ∀ i, Continuous (F i)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p ∈ A, ∀ i, ‖F i 1 - ∫ x, p x • F i x ∂μ‖ < δ := by
  set U : Set Γ := ⋂ i, {x | ‖F i 1 - F i x‖ < δ / 2} with hU
  have hUo : IsOpen U := isOpen_iInter_of_finite fun i => isOpen_lt (continuous_const.sub (hF i)).norm continuous_const
  have h1U : (1 : Γ) ∈ U := mem_iInter.2 fun i => by simpa using hδ
  obtain ⟨φ₀, h0, h1, h01⟩ := exists_continuous_zero_one_of_isClosed hUo.isClosed_compl (isClosed_singleton (x := (1 : Γ)))
    (disjoint_singleton_right.2 fun h => h h1U)
  have hc : 0 < ∫ x, φ₀ x ∂μ :=
    φ₀.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (HasCompactSupport.of_compactSpace _)
      (fun x => (h01 x).1) (by rw [h1 rfl]; exact one_ne_zero)
  set φ : C(Γ, ℝ) := (∫ x, φ₀ x ∂μ)⁻¹ • φ₀ with hφ
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => mul_nonneg (inv_nonneg.2 hc.le) (h01 x).1
  have hφi : Integrable φ μ := φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hφ1 : ∫ x, φ x ∂μ = 1 := by
    simp only [hφ, ContinuousMap.smul_apply, smul_eq_mul]
    rw [integral_const_mul, inv_mul_cancel₀ hc.ne']
  have hM : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖F i x‖ ≤ M := fun i =>
    ⟨‖(⟨F i, hF i⟩ : C(Γ, V))‖, norm_nonneg _, fun x => (⟨F i, hF i⟩ : C(Γ, V)).norm_coe_le_norm x⟩
  choose M hM0 hM using hM
  set Mt : ℝ := (∑ i, M i) * μ.real univ + 1 with hMt
  have hMt0 : 0 < Mt := by
    have : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => hM0 i
    positivity
  obtain ⟨p, hp⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints A hA φ (δ / 2 / Mt)
    (by positivity)
  refine ⟨p, p.2, fun i => ?_⟩
  have e1 : F i 1 - ∫ x, φ x • F i x ∂μ = ∫ x, φ x • (F i 1 - F i x) ∂μ := by
    simp only [smul_sub]
    rw [integral_sub (int_smul μ φ continuous_const) (int_smul μ φ (hF i)), integral_smul_const, hφ1, one_smul]
  have b1 : ‖F i 1 - ∫ x, φ x • F i x ∂μ‖ ≤ δ / 2 := by
    rw [e1]
    refine (norm_integral_le_of_norm_le (hφi.mul_const (δ / 2)) (Eventually.of_forall fun x => ?_)).trans ?_
    · rw [norm_smul, Real.norm_of_nonneg (hφ0 x)]
      by_cases hx : x ∈ U
      · exact mul_le_mul_of_nonneg_left (mem_iInter.1 hx i).le (hφ0 x)
      · have : φ x = 0 := by simp [hφ, h0 hx]
        simp [this]
    · rw [integral_mul_const, hφ1, one_mul]
  have e2 : (∫ x, φ x • F i x ∂μ) - ∫ x, (p : C(Γ, ℝ)) x • F i x ∂μ = ∫ x, (φ x - (p : C(Γ, ℝ)) x) • F i x ∂μ := by
    simp only [sub_smul]
    rw [integral_sub (int_smul μ φ (hF i)) (int_smul μ _ (hF i))]
  have b2 : ‖(∫ x, φ x • F i x ∂μ) - ∫ x, (p : C(Γ, ℝ)) x • F i x ∂μ‖ ≤ ‖(p : C(Γ, ℝ)) - φ‖ * M i * μ.real univ := by
    rw [e2]
    refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => ?_)
    rw [norm_smul, norm_sub_rev]
    exact mul_le_mul (((p : C(Γ, ℝ)) - φ).norm_coe_le_norm x) (hM i x) (norm_nonneg _) (norm_nonneg _)
  have b3 : M i * μ.real univ ≤ Mt := by
    have : M i ≤ ∑ i, M i := Finset.single_le_sum (fun i _ => hM0 i) (Finset.mem_univ i)
    have := mul_le_mul_of_nonneg_right this (measureReal_nonneg (μ := μ) (s := univ))
    linarith
  have b4 : ‖(p : C(Γ, ℝ)) - φ‖ * M i * μ.real univ < δ / 2 := by
    rw [mul_assoc]
    calc _ ≤ ‖(p : C(Γ, ℝ)) - φ‖ * Mt := mul_le_mul_of_nonneg_left b3 (norm_nonneg _)
      _ < δ / 2 := (lt_div_iff₀ hMt0).1 hp
  have := norm_sub_le_norm_sub_add_norm_sub (F i 1) (∫ x, φ x • F i x ∂μ) (∫ x, (p : C(Γ, ℝ)) x • F i x ∂μ)
  linarith
end Formalism.MainStatements.RankOne.KD
