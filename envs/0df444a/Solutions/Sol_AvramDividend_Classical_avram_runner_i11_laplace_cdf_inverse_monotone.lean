-- Prove2me | solution 1 for AvramDividend.Classical.avram_runner_i11_laplace_cdf_inverse_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:37:14.643916+00:00
-- url     : https://prove2.me/submissions/837d3927-7377-4779-a960-8cfc6c5851eb

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_atomless_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (ν : Measure ℝ)
    (hAtom : ∀ x : ℝ, ν {x} = 0)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤)
    (W : ℝ → ℝ)
    (hWzero : W 0 = 0)
    (hWnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hWcont : ContinuousOn W (Ici (0 : ℝ)))
    (b : ℝ)
    (hLap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0)) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) =
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0))) :
    MonotoneOn W (Ici (0 : ℝ)) := by
  let F : ℝ → ℝ := fun x =>
    if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0
  have hFcont : ContinuousOn F (Ici (0 : ℝ)) := by
    exact avram_p4_f6_renewal_cdf_atomless_continuous ν hAtom hFin
  have hFnonneg : ∀ x : ℝ, 0 < x → 0 ≤ F x := by
    intro x hx
    change 0 ≤ if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0
    rw [if_pos (le_of_lt hx)]
    exact ENNReal.toReal_nonneg
  have hEqPos : ∀ x : ℝ, 0 < x → W x = F x := by
    apply continuousOn_Ioi_eq_of_laplace_eq W F b
      (hWcont.mono (by intro x hx; change 0 < x at hx; exact le_of_lt hx))
      (hFcont.mono (by intro x hx; change 0 < x at hx; exact le_of_lt hx))
      (by intro x hx; exact hWnonneg x (le_of_lt hx))
      hFnonneg
    intro θ hθ
    simpa only [F, neg_mul] using hLap θ hθ
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  by_cases hxpos : 0 < x
  · have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
    rw [hEqPos x hxpos, hEqPos y hypos]
    change (if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0) ≤
      (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0)
    rw [if_pos hx, if_pos hy]
    apply ENNReal.toReal_mono (ne_of_lt (hFin y hy))
    exact measure_mono (by
      intro z hz
      exact ⟨hz.1, le_trans hz.2 hxy⟩)
  · have hxeq : x = 0 := le_antisymm (le_of_not_gt hxpos) hx
    subst x
    simpa [hWzero] using hWnonneg y hy
