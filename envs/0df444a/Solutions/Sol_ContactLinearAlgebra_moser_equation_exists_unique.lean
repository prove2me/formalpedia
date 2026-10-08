-- Prove2me | solution 1 for ContactLinearAlgebra.moser_equation_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T15:13:47.958666+00:00
-- url     : https://prove2.me/submissions/6fc86d7d-e2d0-4f76-9792-860f74acac9d

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (a : V →ₗ[ℝ] ℝ) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (ha : ∃ v, a v ≠ 0)
    (hn : ∀ u, a u = 0 → (∀ v, a v = 0 → b u v = 0) → u = 0)
    (β : V →ₗ[ℝ] ℝ) :
    ∃! X : V, a X = 0 ∧ ∃ μ : ℝ, ∀ v, β v + b X v = μ * a v := by
  classical
  let K := a.ker
  let B : K →ₗ[ℝ] Module.Dual ℝ K :=
    { toFun := fun u => (b u).comp K.subtype
      map_add' := by intros; ext v; simp
      map_smul' := by intros; ext v; simp }
  have hker : ∀ u, B u = 0 → u = 0 := by
    intro u hu
    apply Subtype.ext
    apply hn u u.property
    intro v hv
    exact congrArg (fun f : Module.Dual ℝ K => f ⟨v, hv⟩) hu
  have hi : Function.Injective B := LinearMap.ker_eq_bot.mp (by
    ext u
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    exact ⟨hker u, by rintro rfl; exact map_zero B⟩)
  have hs : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := K)).symm).mp hi
  obtain ⟨X, hX⟩ := hs (-(β.comp K.subtype))
  have hz (v : V) (hv : a v = 0) : β v + b X v = 0 := by
    have he := congrArg (fun f : Module.Dual ℝ K => f ⟨v, hv⟩) hX
    change b X v = -β v at he
    linarith
  obtain ⟨w, hw⟩ := ha
  let r := (a w)⁻¹ • w
  have hr : a r = 1 := by simp [r, hw]
  refine ⟨X, ⟨X.property, ⟨β r + b X r, ?_⟩⟩, ?_⟩
  · intro v
    have hv : a (v - a v • r) = 0 := by simp [hr]
    have he := hz (v - a v • r) hv
    simp only [map_sub, map_smul, smul_eq_mul] at he
    nlinarith
  · rintro Y ⟨hY, μ, he⟩
    apply sub_eq_zero.mp
    apply hn (Y - X)
    · simp [hY, X.property]
    · intro v hv
      have h1 := he v
      have h2 := hz v hv
      simp only [hv, mul_zero] at h1
      simp only [map_sub, LinearMap.sub_apply]
      linarith
