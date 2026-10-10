-- Prove2me | solution 1 for ConleyZehnder.argLift_increment_eq_of_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T17:10:14.941562+00:00
-- url     : https://prove2.me/submissions/f0e0c8bd-1b47-4946-8fcd-b085c0e8aa5e

import Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
import Mathlib.Topology.Homotopy.Lifting

open ConleyZehnder

theorem solution
    (H : C(unitInterval × unitInterval, ℂ)) (hH : ∀ p, ‖H p‖ = 1)
    (h0 : ∀ s, H (s, 0) = H (0, 0)) (h1 : ∀ s, H (s, 1) = H (0, 1))
    (θ θ' : unitInterval → ℝ) (hθ : IsArgLift (fun t => H (0, t)) θ)
    (hθ' : IsArgLift (fun t => H (1, t)) θ') :
    θ 1 - θ 0 = θ' 1 - θ' 0 := by
  have hmem : ∀ p, H p ∈ Submonoid.unitSphere ℂ := fun p => by
    simp [Submonoid.unitSphere, hH p]
  let F : C(unitInterval × unitInterval, Circle) :=
    ⟨fun p => ⟨H p, hmem p⟩, H.continuous.subtype_mk _⟩
  let γ₀ : C(unitInterval, Circle) := F.comp ⟨fun t => (0, t), by fun_prop⟩
  let γ₁ : C(unitInterval, Circle) := F.comp ⟨fun t => (1, t), by fun_prop⟩
  let Fh : γ₀.HomotopyRel γ₁ {0, 1} :=
    { toFun := F
      continuous_toFun := F.continuous
      map_zero_left := fun _ => rfl
      map_one_left := fun _ => rfl
      prop' := by
        intro s x hx
        apply Subtype.ext
        rcases hx with rfl | rfl
        · exact h0 s
        · exact h1 s }
  have hexp : ∀ (φ : unitInterval → ℝ) (f : C(unitInterval, Circle)),
      IsArgLift (fun t => (f t : ℂ)) φ → ∀ t, Circle.exp (φ t) = f t := by
    intro φ f hφ t
    apply Subtype.ext
    rw [Circle.coe_exp, ← hφ.2 t]
  have e₀ : γ₀ 0 = Circle.exp (θ 0) := (hexp θ γ₀ hθ 0).symm
  have e₁ : γ₁ 0 = Circle.exp (θ 0) := by
    rw [← e₀]; exact Subtype.ext (h0 1)
  have cov := Circle.isCoveringMap_exp
  have hend := cov.liftPath_apply_one_eq_of_homotopicRel ⟨Fh⟩ (θ 0) e₀ e₁
  have hΓ₀ : (θ : unitInterval → ℝ) = cov.liftPath γ₀ (θ 0) e₀ :=
    (cov.eq_liftPath_iff e₀).2 ⟨hθ.1, funext (hexp θ γ₀ hθ), rfl⟩
  set Γ₁ := cov.liftPath γ₁ (θ 0) e₁
  have hΓ₁ : IsArgLift (fun t => H (1, t)) Γ₁ := by
    refine ⟨Γ₁.continuous, fun t => ?_⟩
    have := congrArg (fun z : Circle => (z : ℂ)) (congrFun (cov.liftPath_lifts γ₁ (θ 0) e₁) t)
    simp only [Function.comp] at this
    rw [← Circle.coe_exp, this]
    rfl
  have hu := (argLift_exists_increment_unique (f := fun t => H (1, t))
    (H.continuous.comp (continuous_const.prodMk continuous_id)) (fun t => hH _)).2 _ _ hΓ₁ hθ'
  have h1' : θ 1 = Γ₁ 1 := by rw [hΓ₀]; exact hend
  have h0' : Γ₁ 0 = θ 0 := cov.liftPath_zero γ₁ (θ 0) e₁
  rw [← hu, h1', h0']
