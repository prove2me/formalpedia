-- Prove2me | solution 2 for CohnElkies.integral_poissonLogistic_change_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:26:33.425361+00:00
-- url     : https://prove2.me/submissions/9d76f462-7e84-4dc1-9e01-afabc12db928

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology


theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    (∫ x : ℝ in Ioo 0 1, f x) =
      ∫ u : ℝ, poissonLogisticDensity u •
        f (poissonLogistic u) := by
  have hpi := Real.pi_pos
  have hP : ∀ u : ℝ, HasDerivAt poissonLogistic (poissonLogisticDensity u) u := by
    intro u
    show HasDerivAt (fun u : ℝ => Real.exp (Real.pi * u) / (1 + Real.exp (Real.pi * u))) _ u
    have he : HasDerivAt (fun u : ℝ => Real.exp (Real.pi * u)) (Real.exp (Real.pi * u) * Real.pi) u := by
      simpa using ((hasDerivAt_id u).const_mul Real.pi).exp
    have h1 : (1 + Real.exp (Real.pi * u)) ≠ 0 := by positivity
    have := he.div (he.const_add 1) h1
    exact this.congr_deriv (by unfold poissonLogisticDensity; field_simp <;> ring)
  have hρ : ∀ u, 0 < poissonLogisticDensity u := fun u => by
    unfold poissonLogisticDensity; positivity
  have hmono : StrictMono poissonLogistic := strictMono_of_hasDerivAt_pos hP hρ
  have hrange : poissonLogistic '' Set.univ = Ioo 0 1 := by
    rw [Set.image_univ]
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      unfold poissonLogistic
      have h := Real.exp_pos (Real.pi * u)
      constructor
      · positivity
      · rw [div_lt_one (by positivity)]; linarith
    · intro hy
      have h1 : 1 - y ≠ 0 := by linarith [hy.2]
      refine ⟨Real.log (y / (1 - y)) / Real.pi, ?_⟩
      unfold poissonLogistic
      rw [show Real.pi * (Real.log (y / (1 - y)) / Real.pi) = Real.log (y / (1 - y)) by field_simp,
        Real.exp_log (div_pos hy.1 (by linarith [hy.2]))]
      field_simp <;> ring
  rw [← hrange, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hP x).hasDerivWithinAt) hmono.injective.injOn f, Measure.restrict_univ]
  congr 1
  funext u
  rw [abs_of_pos (hρ u)]

