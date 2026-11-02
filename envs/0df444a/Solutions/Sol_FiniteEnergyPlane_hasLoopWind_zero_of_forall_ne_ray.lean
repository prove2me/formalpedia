-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopWind_zero_of_forall_ne_ray
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T20:36:33.902787+00:00
-- url     : https://prove2.me/submissions/4876f4c7-cd9c-4574-a269-db120a5fc1c7

import Definitions.Def_FiniteEnergyPlane_Winding



namespace FiniteEnergyPlane

open scoped Real

theorem hasLoopWind_zero_of_forall_ne_ray_aux (q : ℝ → ℂ) (hq : Continuous q)
    (hper : Function.Periodic q 1) (w : ℂ) (hw : w ≠ 0)
    (h : ∀ t, ∀ s : ℝ, 0 ≤ s → q t ≠ s * w) : HasLoopWind q 0 := by
  have hnw : -w ≠ 0 := neg_ne_zero.mpr hw
  have hslit : ∀ t, q t / -w ∈ Complex.slitPlane := by
    intro t
    by_contra hc
    rw [Complex.mem_slitPlane_iff, not_or, not_lt, not_not] at hc
    have hreal : q t / -w = ((q t / -w).re : ℂ) := Complex.ext (by simp only [Complex.ofReal_re]) (by simp only [Complex.ofReal_im]; exact hc.2)
    apply h t (-(q t / -w).re) (by linarith [hc.1])
    calc q t = (q t / -w) * -w := (div_mul_cancel₀ _ hnw).symm
      _ = ((q t / -w).re : ℂ) * -w := by rw [← hreal]
      _ = ((-(q t / -w).re : ℝ) : ℂ) * w := by push_cast; ring
  have hq0 : ∀ t, q t ≠ 0 := fun t ht => h t 0 le_rfl (by simp [ht])
  refine ⟨hq, hper, hq0, fun t => Complex.arg (q t / -w) + Complex.arg (-w), ?_, fun t => ?_, ?_⟩
  · refine Continuous.add ?_ continuous_const
    exact continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (g := Complex.arg) (Complex.continuousAt_arg (hslit t))
        (hq.div_const (-w)).continuousAt
  · have e1 := Complex.norm_mul_exp_arg_mul_I (q t / -w)
    have e2 := Complex.norm_mul_exp_arg_mul_I (-w)
    have hqt : q t = (q t / -w) * -w := (div_mul_cancel₀ _ hnw).symm
    calc q t = (q t / -w) * -w := hqt
      _ = (‖q t / -w‖ * Complex.exp (Complex.arg (q t / -w) * Complex.I)) *
          (‖-w‖ * Complex.exp (Complex.arg (-w) * Complex.I)) := by rw [e1, e2]
      _ = ((‖q t / -w‖ * ‖-w‖ : ℝ) : ℂ) *
          Complex.exp (((Complex.arg (q t / -w) + Complex.arg (-w) : ℝ) : ℂ) * Complex.I) := by
        push_cast
        rw [add_mul, Complex.exp_add]
        ring
      _ = _ := by
        rw [← norm_mul, ← hqt]
  · have h10 : q 1 = q 0 := by simpa using hper 0
    simp [h10]

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution (q : ℝ → ℂ) (hq : Continuous q)
    (hper : Function.Periodic q 1) (w : ℂ) (hw : w ≠ 0)
    (h : ∀ t, ∀ s : ℝ, 0 ≤ s → q t ≠ s * w) : HasLoopWind q 0 :=
  hasLoopWind_zero_of_forall_ne_ray_aux q hq hper w hw h
