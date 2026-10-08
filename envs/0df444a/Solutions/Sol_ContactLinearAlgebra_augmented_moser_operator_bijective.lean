-- Prove2me | solution 1 for ContactLinearAlgebra.augmented_moser_operator_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T19:10:15.867496+00:00
-- url     : https://prove2.me/submissions/2faa52fd-d14f-4935-9959-c01fd632e4b9

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

set_option autoImplicit false

theorem solution {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (D : V →ₗ[ℝ] W) (a : V →ₗ[ℝ] ℝ) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hD : Function.Surjective D) (ha : ∃ v, D v = 0 ∧ a v ≠ 0)
    (hn : ∀ u, D u = 0 → a u = 0 →
      (∀ v, D v = 0 → a v = 0 → b u v = 0) → u = 0) :
    Function.Bijective (fun p : V × (ℝ × Module.Dual ℝ W) =>
      (b p.1 - p.2.1 • a - p.2.2.comp D, (a p.1, D p.1))) := by
  let L : (V × (ℝ × Module.Dual ℝ W)) →ₗ[ℝ]
      (Module.Dual ℝ V × (ℝ × W)) :=
    { toFun := fun p => (b p.1 - p.2.1 • a - p.2.2.comp D, (a p.1, D p.1))
      map_add' := by
        intro p q
        ext v <;> simp [add_smul, LinearMap.sub_apply] <;> ring
      map_smul' := by
        intro r p
        ext v <;> simp [smul_sub, smul_smul, LinearMap.sub_apply] <;> ring }
  have hi : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨u, μ, ν⟩ h
    have hd : D u = 0 := congrArg (fun z => z.2.2) h
    have hau : a u = 0 := congrArg (fun z => z.2.1) h
    have he : ∀ v, b u v - μ * a v - ν (D v) = 0 := by
      intro v
      have hv := congrArg (fun z => z.1 v) h
      simpa [L] using hv
    have hu : u = 0 := hn u hd hau (by
      intro v hdv hav
      simpa [hdv, hav] using he v)
    obtain ⟨v, hdv, hav⟩ := ha
    have hm : μ = 0 := by
      have hv := he v
      simp [hu, hdv] at hv
      exact hv.resolve_right hav
    have hvn : ν = 0 := by
      ext w
      obtain ⟨v, rfl⟩ := hD w
      simpa [hu, hm] using (he v).symm
    simp [hu, hm, hvn]
  have hdim : Module.finrank ℝ (V × (ℝ × Module.Dual ℝ W)) =
      Module.finrank ℝ (Module.Dual ℝ V × (ℝ × W)) := by
    simp [Module.finrank_prod, Subspace.dual_finrank_eq]
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩
