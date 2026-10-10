-- Prove2me | solution 1 for ConleyZehnder.argLift_square_increment
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T21:30:25.160094+00:00
-- url     : https://prove2.me/submissions/3e96a0a8-ada4-43e5-9d68-8dd8db21172a

import Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
import Mathlib.Topology.Homotopy.Lifting

open ConleyZehnder

theorem solution
    (F : C(unitInterval × unitInterval, ℂ)) (hF : ∀ p, ‖F p‖ = 1)
    (a b c d : unitInterval → ℝ)
    (ha : IsArgLift (fun t => F (0, t)) a) (hb : IsArgLift (fun s => F (s, 1)) b)
    (hc : IsArgLift (fun s => F (s, 0)) c) (hd : IsArgLift (fun t => F (1, t)) d) :
    (a 1 - a 0) + (b 1 - b 0) = (c 1 - c 0) + (d 1 - d 0) := by
  have hmem : ∀ p, F p ∈ Submonoid.unitSphere ℂ := fun p => by
    simp [Submonoid.unitSphere, hF p]
  let G : C(unitInterval × unitInterval, Circle) :=
    ⟨fun p => ⟨F p, hmem p⟩, F.continuous.subtype_mk _⟩
  have cov := Circle.isCoveringMap_exp
  let f : C(unitInterval, ℝ) := ⟨a, ha.1⟩
  have hf : ∀ t, G (0, t) = Circle.exp (f t) := fun t => by
    apply Subtype.ext
    show F (0, t) = _
    rw [Circle.coe_exp]; exact ha.2 t
  let Θ := cov.liftHomotopy G f hf
  have hΘ : ∀ p, F p = Complex.exp ((Θ p : ℂ) * Complex.I) := fun p => by
    have := congrArg (fun z : Circle => (z : ℂ)) (congrFun (cov.liftHomotopy_lifts G f hf) p)
    simp only [Function.comp] at this
    rw [← Circle.coe_exp, this]
    rfl
  have edge : ∀ (g : unitInterval → unitInterval × unitInterval), Continuous g →
      ∀ θ : unitInterval → ℝ, IsArgLift (fun t => F (g t)) θ →
        θ 1 - θ 0 = Θ (g 1) - Θ (g 0) := fun g hg θ hθ =>
    (argLift_exists_increment_unique (f := fun t => F (g t)) (F.continuous.comp hg)
      (fun t => hF _)).2 _ _ hθ ⟨Θ.continuous.comp hg, fun t => hΘ (g t)⟩
  rw [edge (fun t => (0, t)) (by fun_prop) a ha, edge (fun s => (s, 1)) (by fun_prop) b hb,
    edge (fun s => (s, 0)) (by fun_prop) c hc, edge (fun t => (1, t)) (by fun_prop) d hd]
  ring
