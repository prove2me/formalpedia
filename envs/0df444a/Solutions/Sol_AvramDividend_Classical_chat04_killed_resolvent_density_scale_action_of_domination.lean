-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_resolvent_density_scale_action_of_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:45:28.622151+00:00
-- url     : https://prove2.me/submissions/7c86ffa1-d41e-4abe-8646-92fdb7ad7401

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_kernel_nonneg_full_halfline
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_density_scale_action_of_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The killed-resolvent kernel acts on a scale function under Laplace domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q p θ : ℝ) (hq : 0 ≤ q) (hp : 0 < p)
    (hθ : 0 ≤ θ) (hroot : X.ψ θ = q + p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hmono : MonotoneOn
      (fun z : ℝ => Real.exp (-(θ * z)) * Wqp z) (Ici (0 : ℝ)))
    (hWq_nonneg : ∀ z : ℝ, 0 ≤ z → 0 ≤ Wq z)
    (hWqp_nonneg : ∀ z : ℝ, 0 ≤ Wqp z)
    (hnegative : ∀ z : ℝ, z < 0 → Wqp z = 0)
    (x : ℝ) (hx : 0 < x)
    (hfirst : IntegrableOn
      (fun y : ℝ => Wq y * (Real.exp (-(θ * y)) * Wqp x))
      (Ioi (0 : ℝ)))
    (hmeas : AEStronglyMeasurable
      (fun y : ℝ => Wq y * Wqp (x - y))
      (volume.restrict (Ioi (0 : ℝ)))) :
    (∫ y in Ioi (0 : ℝ),
      Wq y * (Real.exp (-(θ * y)) * Wqp x - Wqp (x - y))) =
    Wq x / p := by
  have hsecond :
      IntegrableOn (fun y : ℝ => Wq y * Wqp (x - y)) (Ioi (0 : ℝ)) := by
    apply Integrable.mono_nonneg hfirst hmeas
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact mul_nonneg (hWq_nonneg y (le_of_lt hy)) (hWqp_nonneg (x - y))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hker : 0 ≤ Real.exp (-(θ * y)) * Wqp x - Wqp (x - y) :=
        chat04_killed_resolvent_kernel_nonneg_full_halfline
          θ Wqp hmono (fun z _ => hWqp_nonneg z)
          hnegative x y (le_of_lt hx) (le_of_lt hy)
      exact mul_le_mul_of_nonneg_left (sub_nonneg.mp hker)
        (hWq_nonneg y (le_of_lt hy))
  exact chat04_killed_resolvent_density_scale_action_of_integrable
    X hnbv q p θ hq hp hθ hroot Wq Wqp hWq hWqp
    hnegative x hx hfirst hsecond