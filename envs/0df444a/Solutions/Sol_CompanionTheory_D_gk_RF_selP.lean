-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.selP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:36.185232+00:00
-- url     : https://prove2.me/submissions/e7cacef2-159d-4318-a91f-e490ea5890d7

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_CompactIntegralBoundedByQuotientNorm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaL
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_IntegrableMulBc
import Theorems.Thm_CompanionTheory_D_gk_RF_norm_eI
import Theorems.Thm_CompanionTheory_D_gk_RF_eI_add
import Theorems.Thm_CompanionTheory_D_gk_RF_continuous_eI
import Theorems.Thm_CompanionTheory_D_gk_RF_integrable_mul_bc
import Theorems.Thm_CompanionTheory_D_gk_RF_selTw

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
theorem _root_.solution : Sel := by
  intro G _ _ _ _ _ _ _ _ μ _ φ hφ hi N a Ht P F ⟨hFc, M, hM⟩ hN x
  let Fr : ℝ → G → ℂ := fun r y => F (a (r - Ht y) * y)
  have Frc : Continuous fun p : ℝ × G => Fr p.1 p.2 :=
    hFc.comp ((P.cont.comp (continuous_fst.sub (P.hcont.comp continuous_snd))).mul continuous_snd)
  have tw : ∀ r s, ∫ y, φ y * (Fr r (x * y) * eI (s * Ht (x * y))) ∂μ = 0 := fun r s =>
    selTw G μ φ hφ hi N a Ht P s (Fr r) ⟨Frc.comp (continuous_const.prodMk continuous_id), M, fun _ => hM _⟩
      (fun m hm y => by
        have := hN _ (P.norm (r - Ht y) m hm) (a (r - Ht y) * y)
        simp only [Fr, P.hN m hm]
        rw [← this]
        congr 1
        group)
      (fun t y => by
        simp only [Fr, P.ha]
        rw [← mul_assoc, ← P.add]
        congr 3
        ring) x

  have step : ∀ r (g : ℝ → ℂ), Integrable g →
      ∫ y, φ y * Fr r (x * y) * (∫ s, g s * eI (s * (r - Ht (x * y)))) ∂μ = 0 := by
    intro r g hg
    have hc1 : Continuous fun y => Fr r (x * y) := Frc.comp (continuous_const.prodMk (continuous_const.mul continuous_id))
    have hI : Integrable (fun p : G × ℝ => φ p.1 * Fr r (x * p.1) * g p.2 * eI (p.2 * (r - Ht (x * p.1))))
        (μ.prod volume) :=
      ((integrable_mul_bc hφ hc1 fun _ => hM _).mul_prod hg).mul_bdd (c := 1)
        (continuous_eI.comp (continuous_snd.mul (continuous_const.sub
          (P.hcont.comp (continuous_const.mul continuous_fst))))).aestronglyMeasurable
        (Eventually.of_forall fun p => (norm_eI _).le)
    simp only [← integral_const_mul, ← mul_assoc]
    rw [integral_integral_swap hI]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
    have := congrArg (g s * eI (s * r) * ·) (tw r (-s))
    simp only [mul_zero, ← integral_const_mul] at this
    beta_reduce
    rw [Pi.zero_apply, ← this]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [mul_sub, sub_eq_add_neg, eI_add, neg_mul]
    ring
  let ψ : ℝ → ℂ := fun u => ∫ y, φ y * F (a u * (x * y)) ∂μ
  have hc2 : Continuous fun p : ℝ × G => F (a p.1 * (x * p.2)) :=
    hFc.comp ((P.cont.comp continuous_fst).mul (continuous_const.mul continuous_snd))
  have ψc : Continuous ψ :=
    continuous_of_dominated (bound := fun y => ‖φ y‖ * M)
      (fun u => (integrable_mul_bc hφ (hc2.comp (continuous_const.prodMk continuous_id)) fun _ => hM _).aestronglyMeasurable)
      (fun u => Eventually.of_forall fun y => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
      (hφ.norm.mul_const _) (Eventually.of_forall fun y =>
        continuous_const.mul (hc2.comp (continuous_id.prodMk continuous_const)))
  have key : ∀ g ρ : ℝ → ℂ, Integrable g → Integrable ρ → Continuous ρ → (∀ u, ρ u = ∫ s, g s * eI (s * u)) →
      ∫ u, ρ u * ψ u = 0 := by
    intro g ρ hg hρ hρc he
    have hI : Integrable (fun p : G × ℝ => φ p.1 * ρ p.2 * F (a p.2 * (x * p.1))) (μ.prod volume) :=
      (hφ.mul_prod hρ).mul_bdd (c := M) (hc2.comp continuous_swap).aestronglyMeasurable
        (Eventually.of_forall fun _ => hM _)
    have hmp : MeasurePreserving (fun p : G × ℝ => (p.1, p.2 - Ht (x * p.1))) (μ.prod volume) (μ.prod volume) :=
      MeasurePreserving.skew_product (g := fun y r => r - Ht (x * y)) (MeasurePreserving.id μ)
        (continuous_snd.sub (P.hcont.comp (continuous_const.mul continuous_fst))).measurable
        (Eventually.of_forall fun y => (measurePreserving_sub_right volume _).map_eq)
    have hI2 := hmp.integrable_comp_of_integrable hI
    calc ∫ u, ρ u * ψ u = ∫ u, ∫ y, φ y * ρ u * F (a u * (x * y)) ∂μ := by
          simp only [ψ, ← integral_const_mul]
          congr 1; funext u; congr 1; funext y; ring
      _ = ∫ y, (∫ u, φ y * ρ u * F (a u * (x * y))) ∂μ := (integral_integral_swap hI).symm
      _ = ∫ y, (∫ r, φ y * ρ (r - Ht (x * y)) * F (a (r - Ht (x * y)) * (x * y))) ∂μ := by
          congr 1; funext y
          exact (integral_sub_right_eq_self (fun u => φ y * ρ u * F (a u * (x * y))) _).symm
      _ = ∫ r, ∫ y, φ y * ρ (r - Ht (x * y)) * F (a (r - Ht (x * y)) * (x * y)) ∂μ := integral_integral_swap hI2
      _ = 0 := by
          refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
          beta_reduce
          rw [Pi.zero_apply, ← step r g hg]
          congr 1; funext y
          rw [← he]
          simp only [Fr]
          ring
  have hψ : ∀ u, ψ u = 0 := by
    have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := (volume : Measure ℝ)) ψc.locallyIntegrable
      fun ρ hρ hs => by
        let f : SchwartzMap ℝ ℂ := (hs.comp_left (g := Complex.ofReal) rfl).toSchwartzMap
          (Complex.ofRealCLM.contDiff.comp hρ)
        let g : ℝ → ℂ := fun s => ((2 * Real.pi)⁻¹ : ℝ) • FourierTransform.fourier (f : ℝ → ℂ) ((2 * Real.pi)⁻¹ * s)
        have hf : Integrable (FourierTransform.fourier (f : ℝ → ℂ)) := (FourierTransform.fourier f).integrable
        have h2 : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
        have := key g f ((hf.comp_mul_left' h2).smul ((2 * Real.pi)⁻¹ : ℝ)) f.integrable f.continuous fun u => by
          rw [← congrFun (f.continuous.fourierInv_fourier_eq f.integrable hf) u, Real.fourierInv_eq']
          have e := Measure.integral_comp_mul_left
            (fun v => Complex.exp ((2 * Real.pi * inner ℝ v u : ℝ) * Complex.I) • FourierTransform.fourier (f : ℝ → ℂ) v)
            (2 * Real.pi)⁻¹
          rw [inv_inv, abs_of_pos (by positivity)] at e
          rw [← inv_smul_smul₀ (show (2 * Real.pi) ≠ 0 by positivity) (∫ v, _), ← e, ← integral_smul]
          congr 1; funext s
          simp only [g, eI, smul_eq_mul, Complex.real_smul, RCLike.inner_apply, conj_trivial]
          rw [show 2 * Real.pi * (u * ((2 * Real.pi)⁻¹ * s)) = s * u by field_simp]
          ring
        rw [← this]
        simp only [Complex.real_smul]
        rfl
    exact congrFun ((ψc.ae_eq_iff_eq volume continuous_const).1 hae)
  have a0 : a 0 = 1 := by
    have := P.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  simpa [ψ, a0] using hψ 0
end CompanionTheory.D.gk.RF
