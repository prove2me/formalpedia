-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_zero_scale_bounded_contractive_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:19:05.565829+00:00
-- url     : https://prove2.me/submissions/9d77829e-d9ec-45fc-85c5-22fb9cabc50e

import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_zero_scale_tilt_kernel_uniform_bound
import Theorems.Thm_AvramDividend_Classical_zero_scale_kernel_tilt_all_parameter_laplace
import Theorems.Thm_AvramDividend_Classical_unbounded_zero_scale_tilt_kernel_causal_nonnegative
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- An unbounded-variation zero scale supplies a bounded subunit renewal kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q : ℝ) (hq : 0 < q) :
    ∃ θ ρ : ℝ, ∃ K : ℝ → ℝ,
      0 ≤ θ ∧ q < X.ψ θ ∧ 0 < ρ ∧ ρ < 1 ∧
      Continuous K ∧
      BddAbove (Set.range (fun x : ℝ => ‖K x‖)) ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), K x ∂volume) = ρ ∧
      (∀ x : ℝ, x ≤ 0 → K x = 0) ∧
      (∀ x : ℝ, 0 ≤ K x) ∧
      (∀ x : ℝ, K x = q * (Real.exp (-(θ * x)) * W₀ x)) := by
  obtain ⟨θ, hθ, hψall⟩ :=
    chat04_psi_eventually_gt_of_unbounded_variation X q hq hnbv
  have hψq : q < X.ψ θ := hψall θ le_rfl
  have hψ0 : 0 < X.ψ θ := lt_trans hq hψq
  let ρ : ℝ := q / X.ψ θ
  let K : ℝ → ℝ := fun x =>
    q * (Real.exp (-(θ * x)) * W₀ x)
  have hρpos : 0 < ρ := div_pos hq hψ0
  have hρlt : ρ < 1 := (div_lt_one hψ0).2 hψq
  have hWzero : W₀ 0 = 0 :=
    unbounded_scale_zero_origin_nonnegative_discount X hnbv 0 (le_refl 0) W₀ hW₀
  have hWcont : Continuous W₀ :=
    scaleFunction_continuous_of_zero_origin X 0 W₀ hW₀ hWzero
  have hE : Continuous (fun x : ℝ => Real.exp (-(θ * x))) := by
    fun_prop
  have hKcont : Continuous K := by
    dsimp [K]
    exact continuous_const.mul (hE.mul hWcont)
  have hKnorm : BddAbove (Set.range (fun x : ℝ => ‖K x‖)) := by
    exact zero_scale_tilt_kernel_uniform_bound
      X W₀ hW₀ q θ (le_of_lt hq) hθ hψ0
  have hKlap :=
    zero_scale_kernel_tilt_all_parameter_laplace X W₀ hW₀ q θ θ hθ hψ0
  have hKi : IntegrableOn K (Ioi (0 : ℝ)) volume := by
    simpa [K] using hKlap.1
  have hKmass :
      (∫ x in Ioi (0 : ℝ), K x ∂volume) = ρ := by
    simpa [K, ρ] using hKlap.2
  have hsupport :=
    unbounded_zero_scale_tilt_kernel_causal_nonnegative
      X hnbv W₀ hW₀ q θ (le_of_lt hq)
  exact ⟨θ, ρ, K, hθ, hψq, hρpos, hρlt, hKcont,
    hKnorm, hKi, hKmass, hsupport.1, hsupport.2, fun _ => rfl⟩