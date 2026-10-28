-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_resolvent_density_scale_action_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:31:11.709445+00:00
-- url     : https://prove2.me/submissions/8f507649-ee22-42f1-8cfa-f09d4ae600f3

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At zero capital the killed-resolvent spatial kernel vanishes identically. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q p θ : ℝ) (hq : 0 < q) (hp : 0 < p)
    (Wq Wqp : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq)
    (hWqp : IsScaleFunction X (q + p) Wqp)
    (hnegative : ∀ z : ℝ, z < 0 → Wqp z = 0) :
    (∫ y in Ioi (0 : ℝ),
      Wq y * (Real.exp (-(θ * y)) * Wqp 0 - Wqp (0 - y))) =
    Wq 0 / p := by
  have hqp : 0 < q + p := by linarith
  have hWq0 : Wq 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq Wq hWq
  have hWqp0 : Wqp 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv (q + p) hqp Wqp hWqp
  have hI :
      (∫ y in Ioi (0 : ℝ),
        Wq y * (Real.exp (-(θ * y)) * Wqp 0 - Wqp (0 - y))) =
      (∫ _y in Ioi (0 : ℝ), (0 : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hyneg : (0 : ℝ) - y < 0 := by
      have hypos : 0 < y := hy
      linarith
    change Wq y * (Real.exp (-(θ * y)) * Wqp 0 - Wqp (0 - y)) = (0 : ℝ)
    rw [hWqp0, hnegative (0 - y) hyneg]
    ring
  rw [hI]
  simp [hWq0]
