-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.exists_averaging_operator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:31.935801+00:00
-- url     : https://prove2.me/submissions/9f184e2d-81a4-40c5-bcbe-863704d6673f

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_ExistsAvg
import Theorems.Thm_CompanionTheory_D_gk_admitted_integrable_cont
import Theorems.Thm_CompanionTheory_D_gk_admitted_exists_avg
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution : ExistsAvg := by
  intro K _ _ _ _ _ _ _ _ μ _ _ H _ _ _ σ hiso hc S _ hS v hv
  have hcoef : ∀ a b : H, Continuous fun x => ⟪σ x a, b⟫_ℂ := fun a b => (hc a).inner continuous_const
  have hint : ∀ b : H, Integrable (fun x => ⟪σ x v, b⟫_ℂ • σ x v) μ := fun b =>
    integrable_cont ((hcoef v b).smul (hc v))
  have hScl : CompleteSpace S := FiniteDimensional.complete ℂ S

  let L : H →ₗ[ℂ] H :=
    { toFun := fun b => ∫ x, ⟪σ x v, b⟫_ℂ • σ x v ∂μ
      map_add' := fun a b => by
        simp only [inner_add_right, add_smul]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c b => by
        simp only [inner_smul_right, RingHom.id_apply, mul_smul]
        exact integral_smul _ _ }
  have hinner : ∀ w b, ⟪w, L b⟫_ℂ = ∫ x, ⟪σ x v, b⟫_ℂ * ⟪w, σ x v⟫_ℂ ∂μ := by
    intro w b
    change ⟪w, ∫ x, ⟪σ x v, b⟫_ℂ • σ x v ∂μ⟫_ℂ = _
    rw [← integral_inner (hint b)]
    simp only [inner_smul_right]
  have hLS : ∀ b, L b ∈ S := by
    intro b
    rw [← Submodule.orthogonal_orthogonal S, Submodule.mem_orthogonal]
    intro w hw
    rw [hinner]
    have : ∀ x, ⟪w, σ x v⟫_ℂ = 0 := fun x => Submodule.inner_left_of_mem_orthogonal (hS x v hv) hw
    simp [this]
  have hzero : ∀ w, ⟪w, L w⟫_ℂ = 0 → ⟪w, v⟫_ℂ = 0 := by
    intro w hw
    rw [hinner] at hw
    have e1 : ∀ x, ⟪σ x v, w⟫_ℂ * ⟪w, σ x v⟫_ℂ = ((‖⟪σ x v, w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [← inner_conj_symm w, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e1] at hw
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hw
    have hcont : Continuous fun x => ‖⟪σ x v, w⟫_ℂ‖ ^ 2 := (hcoef v w).norm.pow 2
    have h1 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (integrable_cont hcont)).1 hw
    have h2 : ‖⟪σ 1 v, w⟫_ℂ‖ ^ 2 = 0 := congrFun ((hcont.ae_eq_iff_eq μ continuous_const).1 h1) 1
    simp only [map_one, ContinuousLinearMap.one_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, norm_eq_zero] at h2
    exact inner_eq_zero_symm.1 h2
  set R : Submodule ℂ H := S.map L with hR
  have hRc : CompleteSpace R := FiniteDimensional.complete ℂ R
  have hvR : v ∈ R := by
    set w := v - R.starProjection v with hw
    have hwo : w ∈ Rᗮ := R.sub_starProjection_mem_orthogonal v
    have hp : R.starProjection v ∈ R := R.starProjection_apply_mem v
    have hRS : R ≤ S := by rintro _ ⟨b, -, rfl⟩; exact hLS b
    have hwS : w ∈ S := S.sub_mem hv (hRS hp)
    have h1 : ⟪w, v⟫_ℂ = 0 := hzero w (Submodule.inner_left_of_mem_orthogonal (K := R) (Submodule.mem_map_of_mem hwS) hwo)
    have h2 : ⟪w, R.starProjection v⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal hp hwo
    have h3 : ⟪w, w⟫_ℂ = 0 := by
      conv_lhs => rw [hw, inner_sub_right, ← hw]
      rw [h1, h2, sub_zero]
    rw [inner_self_eq_zero, hw, sub_eq_zero] at h3
    rw [h3]; exact hp
  obtain ⟨b, -, hb⟩ := hvR
  obtain ⟨E, hE⟩ := exists_avg (μ := μ) hiso hc (hcoef v b)
  refine ⟨fun x => ⟪σ x v, b⟫_ℂ, E, hcoef v b, ?_, hE, by rw [hE]; exact hb⟩
  let B := Module.finBasis ℂ S
  refine ⟨fun i x => ⟪σ x (B i), b⟫_ℂ, fun i => hcoef _ b, fun k => ?_⟩
  refine ⟨fun i => (starRingEnd ℂ) (B.repr ⟨σ k⁻¹ v, hS _ v hv⟩ i), fun x => ?_⟩
  have e1 : σ k⁻¹ v = ∑ i, B.repr ⟨σ k⁻¹ v, hS _ v hv⟩ i • (B i : H) := by
    have := congrArg Subtype.val (B.sum_repr ⟨σ k⁻¹ v, hS _ v hv⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  show ⟪σ (x * k⁻¹) v, b⟫_ℂ = _
  rw [map_mul, ContinuousLinearMap.mul_apply]
  conv_lhs => rw [e1]
  simp only [map_sum, map_smul, sum_inner, inner_smul_left]
end CompanionTheory.D.gk.admitted
