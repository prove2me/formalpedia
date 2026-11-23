-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.selTw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:44.832129+00:00
-- url     : https://prove2.me/submissions/f4607dc0-f854-4eaa-9154-107a983f119f

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_CompactIntegralBoundedByQuotientNorm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaL
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_IntegrableMulBc
import Theorems.Thm_CompanionTheory_D_gk_RF_idemZero
import Theorems.Thm_CompanionTheory_D_gk_RF_tendsto_transl
import Theorems.Thm_CompanionTheory_D_gk_RF_norm_eI
import Theorems.Thm_CompanionTheory_D_gk_RF_eI_add
import Theorems.Thm_CompanionTheory_D_gk_RF_continuous_eI
import Theorems.Thm_CompanionTheory_D_gk_RF_norm_eI_sub
import Theorems.Thm_CompanionTheory_D_gk_RF_integrable_mul_bc
import Theorems.Thm_CompanionTheory_D_gk_RF_reprod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Filter BoundedContinuousFunction
open scoped ENNReal
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
namespace CompanionTheory.D.gk.RF
theorem _root_.solution : SelTw := by
  intro G _ _ _ _ _ _ _ _ μ _ φ hφ hi N a Ht P
  let X : Submodule ℂ (G →ᵇ ℂ) :=
    { carrier := {F | (∀ m ∈ N, ∀ x, F (m * x) = F x) ∧ ∀ t x, F (a t * x) = F x}
      add_mem' := fun h h' => ⟨fun m hm x => by simp [h.1 m hm, h'.1 m hm], fun t x => by simp [h.2, h'.2]⟩
      zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
      smul_mem' := fun c _ h => ⟨fun m hm x => by simp [h.1 m hm], fun t x => by simp [h.2]⟩ }
  let k : ℝ → (G →ᵇ ℂ) → G → G → ℂ := fun s F x y => F (x * y) * eI (s * (Ht (x * y) - Ht x))
  have kc : ∀ s F, Continuous fun p : G × G => k s F p.1 p.2 := fun s F =>
    (F.continuous.comp continuous_mul).mul (continuous_eI.comp (continuous_const.mul
      ((P.hcont.comp continuous_mul).sub (P.hcont.comp continuous_fst))))
  have kb : ∀ s F x y, ‖k s F x y‖ ≤ ‖F‖ := fun s F x y => by
    simp only [k, norm_mul, norm_eI, mul_one]; exact F.norm_coe_le_norm _
  have ki : ∀ s F x, Integrable (fun y => φ y * k s F x y) μ := fun s F x =>
    integrable_mul_bc hφ ((kc s F).comp (continuous_const.prodMk continuous_id)) (kb s F x)
  let q : ℝ → (G →ᵇ ℂ) → G → ℂ := fun s F x => ∫ y, φ y * k s F x y ∂μ
  have qb : ∀ s F x, ‖q s F x‖ ≤ (∫ y, ‖φ y‖ ∂μ) * ‖F‖ := fun s F x => by
    rw [← integral_mul_const]
    exact norm_integral_le_of_norm_le (hφ.norm.mul_const _) (Eventually.of_forall fun y => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (kb s F x y) (norm_nonneg _))
  have qc : ∀ s F, Continuous (q s F) := fun s F =>
    continuous_of_dominated (bound := fun y => ‖φ y‖ * ‖F‖) (fun x => (ki s F x).aestronglyMeasurable)
      (fun x => Eventually.of_forall fun y => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (kb s F x y) (norm_nonneg _))
      (hφ.norm.mul_const _) (Eventually.of_forall fun y =>
        continuous_const.mul ((kc s F).comp (continuous_id.prodMk continuous_const)))
  let Ql : ℝ → (X →ₗ[ℂ] X) := fun s =>
    { toFun := fun F => ⟨ofNormedAddCommGroup (q s F) (qc s F) _ (qb s F), fun m hm x => by
          show q s F (m * x) = q s F x
          simp only [q, k, mul_assoc m, F.2.1 m hm, P.hN m hm], fun t x => by
          show q s F (a t * x) = q s F x
          simp only [q, k, mul_assoc (a t), F.2.2, P.ha, add_sub_add_left_eq_sub]⟩
      map_add' := fun F F' => Subtype.ext (BoundedContinuousFunction.ext fun x => by
        show q s (F + F') x = q s F x + q s F' x
        rw [← integral_add (ki s F x) (ki s F' x)]
        simp only [q, k, BoundedContinuousFunction.add_apply, add_mul, mul_add])
      map_smul' := fun c F => Subtype.ext (BoundedContinuousFunction.ext fun x => by
        show q s (c • (F : G →ᵇ ℂ)) x = c * q s F x
        rw [← integral_const_mul]
        simp only [q, k, BoundedContinuousFunction.smul_apply, smul_eq_mul]
        exact integral_congr_ae (Eventually.of_forall fun y => by ring)) }
  have hφ0 : 0 ≤ ∫ y, ‖φ y‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  let Q : ℝ → (X →L[ℂ] X) := fun s => (Ql s).mkContinuous (∫ y, ‖φ y‖ ∂μ) fun F =>
    (BoundedContinuousFunction.norm_le (mul_nonneg hφ0 (norm_nonneg _))).2 (qb s F)
  have Qa : ∀ s (F : X) x, (Q s F : G →ᵇ ℂ) x = q s F x := fun _ _ _ => rfl
  have Qn : ∀ (T : X →L[ℂ] X) (d : ℝ), 0 ≤ d → (∀ (F : X) x, ‖(T F : G →ᵇ ℂ) x‖ ≤ d * ‖(F : G →ᵇ ℂ)‖) → ‖T‖ ≤ d :=
    fun T d hd h => T.opNorm_le_bound hd fun F =>
      (BoundedContinuousFunction.norm_le (mul_nonneg hd (norm_nonneg _))).2 (h F)
  obtain ⟨c, hcc, hc⟩ := P.bd
  have hQc : Continuous Q := by
    refine continuous_iff_continuousAt.2 fun s₀ => tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have hI : ∀ s, Integrable (fun y => ‖φ y‖ * min 2 (|s - s₀| * c y)) μ → True := fun _ _ => trivial
    have hc0 : ∀ y, 0 ≤ c y := fun y => (abs_nonneg _).trans (hc 1 y)
    have hb : ∀ s y, ‖‖φ y‖ * min 2 (|s - s₀| * c y)‖ ≤ ‖φ y‖ * 2 := fun s y => by
      rw [norm_mul, norm_norm, Real.norm_of_nonneg (le_min zero_le_two (mul_nonneg (abs_nonneg _) (hc0 y)))]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (norm_nonneg _)
    have hm : ∀ s, AEStronglyMeasurable (fun y => ‖φ y‖ * min 2 (|s - s₀| * c y)) μ := fun s =>
      hφ.norm.aestronglyMeasurable.mul (continuous_const.min (continuous_const.mul hcc)).aestronglyMeasurable
    have hd : Continuous fun s => ∫ y, ‖φ y‖ * min 2 (|s - s₀| * c y) ∂μ :=
      continuous_of_dominated hm (fun s => Eventually.of_forall (hb s)) (hφ.norm.mul_const 2)
        (Eventually.of_forall fun y => by fun_prop)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun s => Qn _ _ (integral_nonneg fun y =>
      mul_nonneg (norm_nonneg _) (le_min zero_le_two (mul_nonneg (abs_nonneg _) (hc0 y)))) fun F x => ?_)
      (by simpa using hd.tendsto s₀)
    show ‖q s F x - q s₀ F x‖ ≤ _
    rw [← integral_sub (ki s F x) (ki s₀ F x), ← integral_mul_const]
    refine norm_integral_le_of_norm_le
      (((hφ.norm.mul_const 2).mono' (hm s) (Eventually.of_forall (hb s))).mul_const _) (Eventually.of_forall fun y => ?_)
    simp only [k]
    rw [← mul_sub, ← mul_sub, norm_mul, norm_mul, mul_assoc, mul_comm (min _ _)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul ((F : G →ᵇ ℂ).norm_coe_le_norm _) ((norm_eI_sub _ _).trans
      (min_le_min le_rfl ?_)) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hc x y) (abs_nonneg _)
  have hQi : ∀ s, Q s * Q s = Q s := fun s => ContinuousLinearMap.ext fun F => Subtype.ext
    (BoundedContinuousFunction.ext fun x => by
      show ∫ y, φ y * (q s F (x * y) * eI (s * (Ht (x * y) - Ht x))) ∂μ = q s F x
      refine Eq.trans ?_ (reprod hφ hi ((kc s F).comp (continuous_const.prodMk continuous_id)) (kb s F x))
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [q, k, Function.comp_apply]
      rw [← integral_mul_const]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [mul_assoc, ← eI_add]
      congr 3
      ring)
  have hQt : Tendsto Q atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 fun e he => ?_
    obtain ⟨τ, hτ, hU⟩ := P.small _ ((tendsto_transl hφ).eventually (gt_mem_nhds he))
    refine ⟨Real.pi / τ + 1, fun s hs => ?_⟩
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
    rw [dist_zero_right]
    refine (Qn _ (e / 2) (by positivity) fun F x => ?_).trans_lt (half_lt_self he)
    obtain ⟨m, hm, hu⟩ := hU (Real.pi / s) (by
      rw [abs_of_pos (by positivity), div_lt_iff₀ hs0, ← div_lt_iff₀' hτ]; linarith) x
    set u := x⁻¹ * (m * a (Real.pi / s)) * x with hu'
    have h1 : ∀ y, k s F x (u * y) = -k s F x y := fun y => by
      have e1 : x * (u * y) = m * (a (Real.pi / s) * (x * y)) := by rw [hu']; group
      simp only [k, e1, F.2.1 m hm, F.2.2, P.hN m hm, P.ha]
      rw [add_sub_assoc, mul_add, eI_add, mul_div_cancel₀ _ hs0.ne']
      simp [eI]
    have h2 : q s F x = -∫ y, φ (u * y) * k s F x y ∂μ := by
      rw [← integral_neg]
      refine (integral_mul_left_eq_self (fun y => φ y * k s F x y) u).symm.trans ?_
      simp only [h1, mul_neg]
    have hi2 : Integrable (fun y => φ (u * y) * k s F x y) μ :=
      integrable_mul_bc (hφ.comp_mul_left u) ((kc s F).comp (continuous_const.prodMk continuous_id)) (kb s F x)
    have h3 : 2 * q s F x = ∫ y, (φ y - φ (u * y)) * k s F x y ∂μ := by
      simp only [sub_mul]
      rw [integral_sub (ki s F x) hi2, two_mul]
      nth_rewrite 2 [h2]
      rfl
    have h4 : ‖2 * q s F x‖ ≤ (∫ y, ‖φ y - φ (u * y)‖ ∂μ) * ‖(F : G →ᵇ ℂ)‖ := by
      rw [h3, ← integral_mul_const]
      exact norm_integral_le_of_norm_le ((hφ.sub (hφ.comp_mul_left u)).norm.mul_const _)
        (Eventually.of_forall fun y => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (kb s F x y) (norm_nonneg _))
    rw [norm_mul, Complex.norm_two] at h4
    rw [Qa]
    have h5 : ∫ y, ‖φ y - φ (u * y)‖ ∂μ < e := hu
    nlinarith [norm_nonneg (F : G →ᵇ ℂ)]
  intro s F ⟨hFc, M, hM⟩ hN ha x
  have h0 := congrArg (fun T : X →L[ℂ] X => (T ⟨ofNormedAddCommGroup F hFc M hM, hN, ha⟩ : G →ᵇ ℂ) x)
    (idemZero _ Q hQc hQi hQt s)
  have h1 : ∫ y, φ y * (F (x * y) * eI (s * (Ht (x * y) - Ht x))) ∂μ = 0 := h0
  have h2 := congrArg (· * eI (s * Ht x)) h1
  simp only [zero_mul, ← integral_mul_const, mul_assoc, ← eI_add] at h2
  rw [← h2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  beta_reduce
  congr 2
  rw [← mul_add, sub_add_cancel]
  rfl
end CompanionTheory.D.gk.RF
