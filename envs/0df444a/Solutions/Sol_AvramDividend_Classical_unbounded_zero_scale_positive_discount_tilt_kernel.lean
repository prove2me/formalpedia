-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_zero_scale_positive_discount_tilt_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:32:02.802203+00:00
-- url     : https://prove2.me/submissions/b3a964fd-c17d-4dfc-b66f-8526d5f6e44b

import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Construct a continuous positive-discount renewal kernel of strictly subunit mass from W0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q : ℝ) (hq : 0 < q) :
    ∃ θ ρ : ℝ, ∃ K : ℝ → ℝ,
      0 ≤ θ ∧ 0 < ρ ∧ ρ < 1 ∧
      Continuous K ∧ IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), K x ∂volume) = ρ ∧
      (∀ x : ℝ, K x = q * (Real.exp (-(θ * x)) * W₀ x)) := by
  obtain ⟨θ, hθ, hθψ⟩ :=
    chat04_psi_eventually_gt_of_unbounded_variation X q hq hnbv
  have hψ : q < X.ψ θ := hθψ θ le_rfl
  have hψpos : 0 < X.ψ θ := lt_trans hq hψ
  have hρpos : 0 < q / X.ψ θ := div_pos hq hψpos
  have hρlt : q / X.ψ θ < 1 := (div_lt_one hψpos).2 hψ
  have hWc : Continuous W₀ :=
    scaleFunction_continuous_of_zero_origin X 0 W₀ hW₀
      (unbounded_scale_zero_origin_nonnegative_discount X hnbv 0 le_rfl W₀ hW₀)
  have hExp : Continuous (fun x : ℝ => Real.exp (-(θ * x))) :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
  have hKc : Continuous (fun x : ℝ =>
      q * (Real.exp (-(θ * x)) * W₀ x)) :=
    continuous_const.mul (hExp.mul hWc)
  have hLap := hW₀.2.2.2.2 θ hθ hψpos
  have hKi : IntegrableOn (fun x : ℝ =>
      q * (Real.exp (-(θ * x)) * W₀ x)) (Ioi (0 : ℝ)) volume :=
    hLap.1.const_mul q
  have hmass :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W₀ x ∂volume) =
        (X.ψ θ)⁻¹ := by simpa using hLap.2
  have hKmass :
      (∫ x in Ioi (0 : ℝ), q * (Real.exp (-(θ * x)) * W₀ x) ∂volume) =
        q / X.ψ θ := by
    rw [integral_const_mul, hmass]
    rw [div_eq_mul_inv]
  exact ⟨θ, q / X.ψ θ, (fun x : ℝ =>
    q * (Real.exp (-(θ * x)) * W₀ x)),
    hθ, hρpos, hρlt, hKc, hKi, hKmass, fun x => rfl⟩
