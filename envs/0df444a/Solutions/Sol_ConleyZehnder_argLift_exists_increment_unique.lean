-- Prove2me | solution 1 for ConleyZehnder.argLift_exists_increment_unique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T16:18:25.501983+00:00
-- url     : https://prove2.me/submissions/6afbd8fe-aaa8-4b8c-9635-64900de04162

import Definitions.Def_ConleyZehnder_Setting
import Mathlib.Topology.Homotopy.Lifting

open ConleyZehnder

theorem solution {f : unitInterval → ℂ} (hf : Continuous f)
    (h1 : ∀ t, ‖f t‖ = 1) :
    (∃ θ, IsArgLift f θ) ∧
      ∀ θ θ', IsArgLift f θ → IsArgLift f θ' → θ 1 - θ 0 = θ' 1 - θ' 0 := by
  have key : ∀ θ : unitInterval → ℝ, IsArgLift f θ → ∀ t,
      Circle.exp (θ t) = ⟨f t, by simp [Submonoid.unitSphere, h1 t]⟩ := by
    intro θ hθ t
    apply Subtype.ext
    rw [Circle.coe_exp, ← hθ.2 t]
  refine ⟨?_, ?_⟩
  · let g : C(unitInterval, Circle) :=
      ⟨fun t => ⟨f t, by simp [Submonoid.unitSphere, h1 t]⟩,
        Continuous.subtype_mk hf (fun t => by simp [Submonoid.unitSphere, h1 t])⟩
    obtain ⟨Γ, hΓ, -⟩ := Circle.isCoveringMap_exp.exists_path_lifts g
      (Complex.arg (g 0 : ℂ)) (Circle.exp_arg (g 0)).symm
    refine ⟨Γ, Γ.continuous, fun t => ?_⟩
    have := congrArg (fun z : Circle => (z : ℂ)) (congrFun hΓ t)
    exact this.symm
  · intro θ θ' hθ hθ'
    have h0 : Circle.exp (θ' 0) = Circle.exp (θ 0) := by rw [key θ hθ, key θ' hθ']
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h0
    have hcomp : Circle.exp ∘ (fun t => θ t + m * (2 * Real.pi)) = Circle.exp ∘ θ' := by
      funext t
      simp only [Function.comp]
      rw [Circle.periodic_exp.int_mul m, key θ hθ, key θ' hθ']
    have heq := Circle.isCoveringMap_exp.eq_of_comp_eq (hθ.1.add continuous_const) hθ'.1
      hcomp 0 (by show θ 0 + _ = θ' 0; rw [hm])
    have e1 := congrFun heq 1
    have e0 := congrFun heq 0
    change θ 1 + _ = θ' 1 at e1
    linarith
