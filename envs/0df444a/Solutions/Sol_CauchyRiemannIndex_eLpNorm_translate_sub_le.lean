-- Prove2me | solution 1 for CauchyRiemannIndex.eLpNorm_translate_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T08:19:01.973339+00:00
-- url     : https://prove2.me/submissions/7bc58d37-b255-400f-887c-78f3ef050334

import Mathlib

-- ===== Scratch/CRRelA.lean =====
/-!
# `‖g(· + h) - g‖_p ≤ |h| ‖Dg‖_p` for `C¹` maps on `ℝᵐ`

Pointwise: fundamental theorem of calculus on `τ ↦ g (x + τ h)`; then Jensen on `[0, 1]`,
Tonelli and translation invariance of Lebesgue measure.
-/

namespace CauchyRiemannIndex

open MeasureTheory Set
open scoped ENNReal NNReal

lemma crra_jensen {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {p : ℝ} (hp : 1 ≤ p) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) ^ p ≤ ∫⁻ a, f a ^ p ∂μ := by
  rcases hp.eq_or_lt with h | hp
  · subst h; simp
  have hpq := Real.HolderConjugate.conjExponent hp
  set q := p.conjExponent with hq
  have hq0 : 0 < q := hpq.symm.pos
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul,
    measure_univ, ENNReal.one_rpow, mul_one] at h
  have hp0 : 0 < p := by linarith
  calc (∫⁻ a, f a ∂μ) ^ p ≤ ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h hp0.le
    _ = ∫⁻ a, f a ^ p ∂μ := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]

variable {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma crra_pointwise {g : EuclideanSpace ℝ (Fin m) → F} (hg : ContDiff ℝ 1 g)
    (h x : EuclideanSpace ℝ (Fin m)) :
    ‖g (x + h) - g x‖ₑ ≤
      ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + τ • h)‖ₑ * ‖h‖ₑ := by
  have hd : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => g (x + τ • h)) (fderiv ℝ g (x + τ • h) h) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => x + τ • h) h τ := by
      simpa using ((hasDerivAt_id τ).smul_const h).const_add x
    have h2 := (hg.differentiable one_ne_zero (x + τ • h)).hasFDerivAt
    exact h2.comp_hasDerivAt τ h1
  have hcont : Continuous fun τ : ℝ => fderiv ℝ g (x + τ • h) h := by
    have := hg.continuous_fderiv one_ne_zero
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hd τ)
    (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero] at hftc
  rw [← hftc, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun τ => ?_)
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)

theorem crra_main (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (g : EuclideanSpace ℝ (Fin m) → F) (hg : ContDiff ℝ 1 g) (h : EuclideanSpace ℝ (Fin m)) :
    eLpNorm (fun x => g (x + h) - g x) p volume ≤
      ENNReal.ofReal ‖h‖ * eLpNorm (fun x => ‖fderiv ℝ g x‖) p volume := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  have hpr0 : 0 < p.toReal := by linarith
  set r := p.toReal
  have hcD : Continuous fun x => fderiv ℝ g x := hg.continuous_fderiv one_ne_zero
  haveI : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  -- pointwise bound after Jensen
  have hpt : ∀ x, ‖g (x + h) - g x‖ₑ ^ r ≤
      ‖h‖ₑ ^ r * ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + τ • h)‖ₑ ^ r := by
    intro x
    have hm : AEMeasurable (fun τ : ℝ => ‖fderiv ℝ g (x + τ • h)‖ₑ * ‖h‖ₑ)
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      ((by fun_prop : Continuous fun τ : ℝ => ‖fderiv ℝ g (x + τ • h)‖ₑ).measurable.mul_const
        _).aemeasurable
    calc ‖g (x + h) - g x‖ₑ ^ r
        ≤ (∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + τ • h)‖ₑ * ‖h‖ₑ) ^ r :=
          ENNReal.rpow_le_rpow (crra_pointwise hg h x) hpr0.le
      _ ≤ ∫⁻ τ in Ioc (0 : ℝ) 1, (‖fderiv ℝ g (x + τ • h)‖ₑ * ‖h‖ₑ) ^ r :=
          crra_jensen _ hpr hm
      _ = ‖h‖ₑ ^ r * ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + τ • h)‖ₑ ^ r := by
          rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hpr0.le enorm_ne_top)]
          congr 1; funext τ
          rw [ENNReal.mul_rpow_of_nonneg _ _ hpr0.le, mul_comm]
  -- Tonelli + translation invariance
  have hswap : ∫⁻ x, ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + τ • h)‖ₑ ^ r =
      ∫⁻ x, ‖fderiv ℝ g x‖ₑ ^ r := by
    rw [lintegral_lintegral_swap]
    · have : ∀ τ : ℝ, ∫⁻ x, ‖fderiv ℝ g (x + τ • h)‖ₑ ^ r = ∫⁻ x, ‖fderiv ℝ g x‖ₑ ^ r :=
        fun τ => lintegral_add_right_eq_self (fun x => ‖fderiv ℝ g x‖ₑ ^ r) (τ • h)
      simp only [this, lintegral_const, measure_univ, mul_one, Measure.restrict_apply_univ,
        Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]
    · have : Continuous fun z : EuclideanSpace ℝ (Fin m) × ℝ => ‖fderiv ℝ g (z.1 + z.2 • h)‖ₑ :=
        by fun_prop
      exact (this.measurable.pow_const r).aemeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp',
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']
  have hnorm : ∀ x, ‖(‖fderiv ℝ g x‖)‖ₑ = ‖fderiv ℝ g x‖ₑ := fun x => by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_norm]
  simp only [hnorm]
  calc (∫⁻ x, ‖g (x + h) - g x‖ₑ ^ r) ^ (1 / r)
      ≤ (∫⁻ x, ‖h‖ₑ ^ r * ∫⁻ τ in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + τ • h)‖ₑ ^ r) ^ (1 / r) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by positivity)
    _ = (‖h‖ₑ ^ r * ∫⁻ x, ‖fderiv ℝ g x‖ₑ ^ r) ^ (1 / r) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hpr0.le enorm_ne_top), hswap]
    _ = ENNReal.ofReal ‖h‖ * (∫⁻ x, ‖fderiv ℝ g x‖ₑ ^ r) ^ (1 / r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hpr0.ne', ENNReal.rpow_one, ofReal_norm_eq_enorm]

end CauchyRiemannIndex

-- ===== Scratch/CRRelASol.lean =====
open MeasureTheory CauchyRiemannIndex
open scoped ENNReal NNReal

theorem solution {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (g : EuclideanSpace ℝ (Fin m) → F) (hg : ContDiff ℝ 1 g) (h : EuclideanSpace ℝ (Fin m)) :
    eLpNorm (fun x => g (x + h) - g x) p volume ≤
      ENNReal.ofReal ‖h‖ * eLpNorm (fun x => ‖fderiv ℝ g x‖) p volume :=
  crra_main p hp hp' g hg h
