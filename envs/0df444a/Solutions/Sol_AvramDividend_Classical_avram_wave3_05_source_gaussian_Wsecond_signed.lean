-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_source_gaussian_Wsecond_signed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:25:37.138987+00:00
-- url     : https://prove2.me/submissions/9973dd5b-8a50-417c-ae88-908c7c9e57a5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_native_double_tail_kernel_full_regularity
import Theorems.Thm_AvramDividend_Classical_gaussian_native_levy_esscher_double_tail_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_canonical_volterra_identity_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_positive_indicator_continuous
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_volterra_deriv_eq_resolvent_on_positive
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_volterra_resolvent_signed_deriv
import Theorems.Thm_AvramDividend_Classical_causal_volterra_C2_of_C1_derivative_resolvent
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_esscher_untilting_second_deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original Gaussian q-scale has a globally integrable exact second-derivative density. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (a w : ℝ) (S : ℝ → ℝ),
      0 < a ∧
      IntegrableOn S (Ioi (0 : ℝ)) volume ∧
      (∀ x : ℝ, 0 < x →
        deriv (deriv W) x =
          2 * φ * deriv W x - φ ^ 2 * W x +
            Real.exp ((φ + w) * x) * (S x / a)) := by
  let a : ℝ := X.σ ^ 2 / 2
  let β : ℝ :=
    X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
      X.σ ^ 2 * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
        ∂(X.ν.map (fun y : ℝ => -y)))
  let K : ℝ → ℝ := fun t : ℝ =>
    (∫⁻ z : ℝ,
      if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
      else 0 ∂(X.ν.map (fun y : ℝ => -y))).toReal
  let V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (pow_pos hσ 2) (by norm_num)
  have hKreg : Integrable K volume ∧
      ContinuousOn K (Ioi (0 : ℝ)) ∧
      AntitoneOn K (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, 0 < t → 0 ≤ K t) := by
    simpa only [K] using
      (gaussian_native_double_tail_kernel_full_regularity X φ hφ)
  rcases hKreg with ⟨_, hKcont, hKanti, hKpos⟩
  have hKint : IntegrableOn K (Ioi (0 : ℝ)) volume := by
    simpa only [K] using
      (gaussian_native_levy_esscher_double_tail_integrable X φ hφ)
  have hKposAll : ∀ t : ℝ, 0 ≤ t → 0 ≤ K t := by
    intro t _
    dsimp [K]
    exact ENNReal.toReal_nonneg
  have hVEq : ∀ x : ℝ, 0 < x →
      a * V x + (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * V s ∂volume) = x := by
    exact gaussian_esscher_canonical_volterra_identity_of_positive_sigma
      X q hq W hW hσ φ hφ hroot V (by intro x _; rfl) a β K rfl rfl rfl
  obtain ⟨T, g, w, hForm, hgc, hgC1, hge, hTL1, hGder⟩ :=
    avram_wave3_05_gaussian_volterra_resolvent_signed_deriv
      K a β ha hKint hKposAll hKanti hKcont
  have hVind : Continuous ((Ioi (0 : ℝ)).indicator V) :=
    gaussian_esscher_positive_indicator_continuous
      X q hq W hW hσ φ V (by intro x _; rfl)
  have hVc : ContinuousOn V (Ioi (0 : ℝ)) := by
    refine hVind.continuousOn.congr ?_
    intro x hx
    simp only [Set.indicator_of_mem hx]
  have hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C :=
    gaussian_esscher_tilted_scale_locally_bounded
      X q hq W hW hσ φ hφ V (by intro x _; rfl)
  have hder := causal_volterra_deriv_eq_resolvent_on_positive
    K g V a β ha hKint hVc hVb hVEq hgc hge

  have hVc2 : ContDiffOn ℝ 2 V (Ioi (0 : ℝ)) :=
    causal_volterra_C2_of_C1_derivative_resolvent
      K g V a β ha hKint hVc hVb hVEq hgc hgC1 hge
  have hVdiff : DifferentiableOn ℝ V (Ioi (0 : ℝ)) :=
    hVc2.differentiableOn (by norm_num)
  have hVHasDeriv : ∀ x : ℝ, 0 < x → HasDerivAt V (g x) x := by
    intro x hx
    have hd :=
      (hVdiff.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
    rw [hder x hx] at hd
    exact hd
  have hWrepr : (fun z : ℝ => Real.exp (φ * z) * V z) = W := by
    funext z
    dsimp [V]
    rw [← mul_assoc, ← Real.exp_add]
    have hzero : φ * z + -(φ * z) = 0 := by ring
    rw [hzero, Real.exp_zero, one_mul]
  have hsecond0 :=
    avram_wave3_05_esscher_untilting_second_deriv
      V g (fun x : ℝ => ∑' n : ℕ, T n x) φ w a
      hVHasDeriv hGder
  refine ⟨a, w, (fun x : ℝ => ∑' n : ℕ, T n x), ha, hTL1, ?_⟩
  intro x hx
  have hx2 := hsecond0 x hx
  change deriv (deriv (fun z : ℝ => Real.exp (φ * z) * V z)) x =
    2 * φ * deriv (fun z : ℝ => Real.exp (φ * z) * V z) x -
      φ ^ 2 * (Real.exp (φ * x) * V x) +
      Real.exp ((φ + w) * x) *
        ((∑' n : ℕ, T n x) / a) at hx2
  have hValue : Real.exp (φ * x) * V x = W x :=
    congrFun hWrepr x
  rw [hWrepr, hValue] at hx2
  exact hx2
